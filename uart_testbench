`timescale 1ns/1ps

`include "interface.sv"
`include "environment.sv"
// `include "uart_design.sv"  // Uncomment if all design files are in one file

module testbench;

  //---------------------------------------------
  // CLOCK & RESET
  //---------------------------------------------
  logic clk;
  logic rst;

  // 100 MHz clock (10 ns period)
  initial clk = 0;
  always #5 clk = ~clk;

  // Reset generation
  initial begin
    rst = 1;
    #20;
    rst = 0; // release reset after 20 ns
  end

  //---------------------------------------------
  // INTERFACE INSTANTIATION
  //---------------------------------------------
  uart_if uart_if_inst (clk, rst);

  //---------------------------------------------
  // DUT CONNECTIONS
  //---------------------------------------------
  logic tx_enb, rx_enb;
  baud_rate_generator baud_gen (
    .clk    (clk),
    .rst_n  (~rst),
    .tx_enb (tx_enb),
    .rx_enb (rx_enb)
  );

  // TX internal signals
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

  tx_fsm u_tx_fsm (
    .clk        (clk),
    .rst        (rst),
    .TXstart    (uart_if_inst.TXstart),
    .parity_bit (parity_bit),
    .data_bit   (data_bit),
    .load       (load),
    .shift      (shift),
    .sel        (sel),
    .TX_busy    (uart_if_inst.TX_busy)
  );

  // TX output line
  logic tx_line;
  always_comb begin
    case (sel)
      2'b00: tx_line = 1'b0;        // Start bit
      2'b01: tx_line = data_bit;    // Data bits
      2'b10: tx_line = parity_bit;  // Parity bit
      2'b11: tx_line = 1'b1;        // Stop bit
      default: tx_line = 1'b1;
    endcase
  end

  assign uart_if_inst.TX_data_out = tx_line;
  assign uart_if_inst.RX_in       = tx_line; // loopback

  //---------------------------------------------
  // RX path
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
    .clk           (clk),
    .rst           (rst),
    .check         (parity_check),
    .data_in       (uart_if_inst.RX_data_out),
    .sampled_parity(uart_if_inst.RX_in),
    .parity_err    (uart_if_inst.parity_err)
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
    env.run(); // optional
  end

  //---------------------------------------------
  // MANUAL TEST STIMULUS
  //---------------------------------------------
  initial begin
    @(negedge rst);
    #50;

    $display("\n=== UART TEST STARTED ===");

    // 1️⃣ First Byte
    wait (!uart_if_inst.TX_busy);
    @(posedge clk);
    uart_if_inst.TX_data_in = 8'hA5;
    uart_if_inst.TXstart = 1;
    @(posedge clk);
    uart_if_inst.TXstart = 0;
    $display("[%0t ns] Sent first byte: 0xA5", $time);

    wait (!uart_if_inst.TX_busy);
    repeat (5) @(posedge clk);

    // 2️⃣ Second Byte
    uart_if_inst.TX_data_in = 8'h3C;
    uart_if_inst.TXstart = 1;
    @(posedge clk);
    uart_if_inst.TXstart = 0;
    $display("[%0t ns] Sent second byte: 0x3C", $time);

    wait (uart_if_inst.data_ready);
    $display("[%0t ns] Data received: 0x%0h", $time, uart_if_inst.RX_data_out);

    wait (!uart_if_inst.TX_busy);
    repeat (5) @(posedge clk);

    // 3️⃣ Third Byte
    uart_if_inst.TX_data_in = 8'hF0;
    uart_if_inst.TXstart = 1;
    @(posedge clk);
    uart_if_inst.TXstart = 0;
    $display("[%0t ns] Sent third byte: 0xF0", $time);

    wait (uart_if_inst.data_ready);
    $display("[%0t ns] Final Data received: 0x%0h", $time, uart_if_inst.RX_data_out);

        #50000;
    $display("=== UART TEST COMPLETED ===\n");
    $finish;
  end  // <- closes the manual stimulus initial block


  //---------------------------------------------
  // COVERAGE DISPLAY BLOCK
  //---------------------------------------------
  initial begin
    #100000;
    $display("============================================");
    $display(" UART Transaction Coverage = %0.2f%%", env.mon.tr.trans_cov.get_coverage());
    $display(" Overall Coverage          = %0.2f%%", $get_coverage());
    $display("============================================");
  end


  //---------------------------------------------
  // WAVEFORM DUMP
  //---------------------------------------------
  initial begin
    $dumpfile("uart_wave.vcd");
    $dumpvars(1, testbench);
  end

endmodule
