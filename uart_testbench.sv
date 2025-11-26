`timescale 1ns/1ps

`include "interface.sv"
`include "environment.sv"

module testbench;

  //---------------------------------------------
  // CLOCK & RESET
  //---------------------------------------------
  logic clk;
  logic rst;

  initial clk = 0;
  always #5 clk = ~clk;   // 100 MHz

  initial begin
    rst = 1;
    #20 rst = 0;
  end


  //---------------------------------------------
  // INTERFACE
  //---------------------------------------------
  uart_if uart_if_inst (clk, rst);


  //---------------------------------------------
  // BAUD GENERATOR
  //---------------------------------------------
  logic tx_enb, rx_enb;

  baud_rate_generator #(.TX_DIV(10), .RX_DIV(10)) baud_gen (
    .clk   (clk),
    .rst_n (~rst),
    .tx_enb(tx_enb),
    .rx_enb(rx_enb)
  );


  //---------------------------------------------
  // TX PATH
  //---------------------------------------------
  logic parity_bit, load, shift;
  logic [1:0] sel;
  logic data_bit;

  parity_gen u_parity (
    .data_in    (uart_if_inst.TX_data_in),
    .parity_bit (parity_bit)
  );

  piso u_piso (
    .clk        (clk),
    .rst        (rst),
    .load       (load),
    .shift      (shift),
    .data_in    (uart_if_inst.TX_data_in),
    .serial_out (data_bit)
  );

  // *** Corrected TX FSM ***
  tx_fsm u_tx_fsm (
    .clk        (clk),
    .rst        (rst),
    .TXstart    (uart_if_inst.TXstart),
    .tx_enb     (tx_enb),        // << required
    .parity_bit (parity_bit),
    .data_bit   (data_bit),
    .load       (load),
    .shift      (shift),
    .sel        (sel),
    .TX_busy    (uart_if_inst.TX_busy)
  );

  logic tx_line;
  always_comb begin
    case (sel)
      2'b00: tx_line = 1'b0;         // start
      2'b01: tx_line = data_bit;     // data
      2'b10: tx_line = parity_bit;   // parity
      2'b11: tx_line = 1'b1;         // stop/idle
      default: tx_line = 1'b1;
    endcase
  end

  assign uart_if_inst.TX_data_out = tx_line;
  assign uart_if_inst.RX_in       = tx_line;     // loopback


  //---------------------------------------------
  // RX PATH
  //---------------------------------------------
  logic start_detected, shift_rx, parity_check, stop_check;

  start_bit_detect_sync u_start (
    .clk            (clk),
    .rst            (rst),
    .RX_in          (uart_if_inst.RX_in),
    .start_detected (start_detected)
  );

  sipo_simple u_sipo (
    .clk         (clk),
    .rst         (rst),
    .shift       (shift_rx),
    .sampled_bit (uart_if_inst.RX_in),
    .data_out    (uart_if_inst.RX_data_out)
  );

  parity_check_simple u_parity_chk (
    .clk            (clk),
    .rst            (rst),
    .check          (parity_check),
    .data_in        (uart_if_inst.RX_data_out),
    .sampled_parity (uart_if_inst.RX_in),
    .parity_err     (uart_if_inst.parity_err)
  );

  stop_check_simple u_stop_chk (
    .clk          (clk),
    .rst          (rst),
    .check        (stop_check),
    .sampled_stop (uart_if_inst.RX_in),
    .stop_err     (uart_if_inst.stop_err)
  );

  rx_fsm_simple u_rx_fsm (
    .clk           (clk),
    .rst           (rst),
    .start_detected(start_detected),
    .sample_tick   (rx_enb),
    .rx_in         (uart_if_inst.RX_in),
    .shift         (shift_rx),
    .parity_check  (parity_check),
    .stop_check    (stop_check),
    .data_ready    (uart_if_inst.data_ready)
  );


  //---------------------------------------------
  // ENVIRONMENT
  //---------------------------------------------
  uart_env env;
  initial begin
    env = new(uart_if_inst);
    env.run();
  end


  //---------------------------------------------
  // SEND TASK (BAUD-ALIGNED)
  //---------------------------------------------
  task automatic send_byte(input logic [7:0] b);
  begin
    // wait for transmitter to be idle
    wait (!uart_if_inst.TX_busy);

    // put data on interface before asserting start
    uart_if_inst.TX_data_in = b;

    // align assertion to baud boundary
    @(posedge tx_enb);
    uart_if_inst.TXstart = 1;

    // hold TXstart for 1 baud tick so FSM sees it on a tx_enb
    @(posedge tx_enb);
    uart_if_inst.TXstart = 0;
  end
  endtask


  //---------------------------------------------
  // MANUAL STIMULUS (USING send_byte)
  //---------------------------------------------
  initial begin
    @(negedge rst);
    #50;

    $display("\n=== UART TEST STARTED ===");

    send_byte(8'hA5);
    wait (uart_if_inst.data_ready);
    $display("[%0t ns] RX: %02h", $time, uart_if_inst.RX_data_out);

    send_byte(8'h3C);
    wait (uart_if_inst.data_ready);
    $display("[%0t ns] RX: %02h", $time, uart_if_inst.RX_data_out);

    send_byte(8'hF0);
    wait (uart_if_inst.data_ready);
    $display("[%0t ns] RX: %02h", $time, uart_if_inst.RX_data_out);

    #20000;
    $display("\n=== UART TEST COMPLETED ===");
    $finish;
  end


  //---------------------------------------------
  // COVERAGE DISPLAY BLOCK  (FULLY ENABLED)
  //---------------------------------------------
  initial begin
    #100000;

    $display("============================================");
    if (env.mon.tr.trans_cov != null)
      $display(" UART Transaction Coverage = %0.2f%%",
               env.mon.tr.trans_cov.get_coverage());
    else
      $display(" UART Transaction Coverage = Monitor not enabled");

    $display(" Overall Coverage          = %0.2f%%",
             $get_coverage());
    $display("============================================");
  end


  //---------------------------------------------
  // WAVEFORM
  //---------------------------------------------
  initial begin
    $dumpfile("uart_wave.vcd");
    $dumpvars(0, testbench);
  end

endmodule
