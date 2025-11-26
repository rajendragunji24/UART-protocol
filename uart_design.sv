`timescale 1ns/1ps

//==================================================
// 1. BAUD RATE GENERATOR
//==================================================
module baud_rate_generator #(
  parameter int TX_DIV = 10,
  parameter int RX_DIV = 10
)(
  input  logic clk,
  input  logic rst_n,
  output logic tx_enb,
  output logic rx_enb
);

  // sized counters (guard against TX_DIV==1 with $clog2)
  localparam int TX_CNTW = ($clog2(TX_DIV) == 0) ? 1 : $clog2(TX_DIV);
  localparam int RX_CNTW = ($clog2(RX_DIV) == 0) ? 1 : $clog2(RX_DIV);

  logic [TX_CNTW-1:0] tx_counter;
  logic [RX_CNTW-1:0] rx_counter;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) tx_counter <= '0;
    else if (tx_counter == TX_DIV-1) tx_counter <= '0;
    else tx_counter <= tx_counter + 1'b1;
  end

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) rx_counter <= '0;
    else if (rx_counter == RX_DIV-1) rx_counter <= '0;
    else rx_counter <= rx_counter + 1'b1;
  end

  assign tx_enb = (tx_counter == TX_DIV-1);
  assign rx_enb = (rx_counter == RX_DIV-1);

endmodule


//==================================================
// 2. PARITY GENERATOR (even parity)
//==================================================
module parity_gen (
  input  logic [7:0] data_in,
  output logic       parity_bit
);
  always_comb parity_bit = ^data_in;
endmodule


//==================================================
// 3. PISO (Parallel-In Serial-Out)
//==================================================
module piso (
  input  logic       clk,
  input  logic       rst,
  input  logic       load,
  input  logic       shift,
  input  logic [7:0] data_in,
  output logic       serial_out
);

  logic [7:0] shift_reg;

  always_ff @(posedge clk or posedge rst) begin
    if (rst) shift_reg <= 8'd0;
    else if (load) shift_reg <= data_in;
    else if (shift) shift_reg <= {1'b0, shift_reg[7:1]};
  end

  assign serial_out = shift_reg[0];

endmodule


//==================================================
// 4. TX FSM (FINAL CORRECT VERSION)
//==================================================
module tx_fsm (
  input  logic clk,
  input  logic rst,
  input  logic TXstart,
  input  logic tx_enb,
  input  logic parity_bit,
  input  logic data_bit,
  output logic load,
  output logic shift,
  output logic [1:0] sel,
  output logic TX_busy
);

  typedef enum logic [2:0] {IDLE, START, DATA, PARITY, STOP} state_t;
  state_t current_state, next_state;

  logic [3:0] bit_count; // 0..8 safe

  // state register
  always_ff @(posedge clk or posedge rst) begin
    if (rst) current_state <= IDLE;
    else     current_state <= next_state;
  end

  // next state logic
  always_comb begin
    next_state = current_state;
    case (current_state)
      IDLE:   if (TXstart) next_state = START;
      START:  if (tx_enb) next_state = DATA;
      DATA:   if (tx_enb && (bit_count == 4'd7)) next_state = PARITY; // after 8 bits (0..7)
      PARITY: if (tx_enb) next_state = STOP;
      STOP:   if (tx_enb) next_state = IDLE;
    endcase
  end

  // outputs and counters (synchronous)
  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      load      <= 1'b0;
      shift     <= 1'b0;
      sel       <= 2'b11;
      TX_busy   <= 1'b0;
      bit_count <= 4'd0;
    end
    else begin
      // defaults each cycle
      load  <= 1'b0;
      shift <= 1'b0;
      sel   <= 2'b11; // default to idle/stop

      case (current_state)

        IDLE: begin
          TX_busy <= 1'b0;
          bit_count <= 4'd0;
          // only load if TXstart aligns with a baud tick
          if (TXstart && tx_enb) begin
            load <= 1'b1;
            TX_busy <= 1'b1;
            // bit_count stays 0; START will be issued next
          end
        end

        START: begin
          sel <= 2'b00;
          // we move to DATA on tx_enb (next_state logic)
        end

        DATA: begin
          sel <= 2'b01;
          if (tx_enb) begin
            shift <= 1'b1;                  // one shift per baud tick
            bit_count <= bit_count + 1'b1;
          end
        end

        PARITY: begin
          sel <= 2'b10;
          // parity output presented for one tx_enb cycle (next_state handles move)
        end

        STOP: begin
          sel <= 2'b11;
          if (tx_enb) begin
            TX_busy <= 1'b0;
            bit_count <= 4'd0;
          end
        end

      endcase
    end
  end

endmodule


//==================================================
// 5. START BIT DETECTOR (synchronizer + falling edge detect)
//==================================================
module start_bit_detect_sync (
  input  logic clk,
  input  logic rst,
  input  logic RX_in,
  output logic start_detected
);

  logic rx_sync0, rx_sync1, rx_prev;

  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin rx_sync0 <= 1'b1; rx_sync1 <= 1'b1; end
    else begin rx_sync0 <= RX_in; rx_sync1 <= rx_sync0; end
  end

  always_ff @(posedge clk or posedge rst) begin
    if (rst) rx_prev <= 1'b1;
    else     rx_prev <= rx_sync1;
  end

  always_ff @(posedge clk or posedge rst) begin
    if (rst) start_detected <= 1'b0;
    else     start_detected <= (rx_prev && ~rx_sync1);
  end

endmodule


//==================================================
// 6. SIPO (Serial-In Parallel-Out)
//==================================================
module sipo_simple #(
  parameter WIDTH = 8
)(
  input  logic clk,
  input  logic rst,
  input  logic shift,
  input  logic sampled_bit,
  output logic [WIDTH-1:0] data_out
);

  always_ff @(posedge clk or posedge rst) begin
    if (rst) data_out <= '0;
    else if (shift) data_out <= {sampled_bit, data_out[WIDTH-1:1]};
  end

endmodule


//==================================================
// 7. PARITY CHECK
//==================================================
module parity_check_simple #(
  parameter WIDTH = 8,
  parameter bit ODD_PARITY = 1'b0
)(
  input  logic clk,
  input  logic rst,
  input  logic check,
  input  logic [WIDTH-1:0] data_in,
  input  logic sampled_parity,
  output logic parity_err
);

  logic parity_xor;
  always_comb parity_xor = ^data_in;

  always_ff @(posedge clk or posedge rst) begin
    if (rst) parity_err <= 1'b0;
    else if (check) parity_err <= (sampled_parity != (ODD_PARITY ? ~parity_xor : parity_xor));
    else parity_err <= 1'b0;
  end

endmodule


//==================================================
// 8. STOP CHECK
//==================================================
module stop_check_simple (
  input  logic clk,
  input  logic rst,
  input  logic check,
  input  logic sampled_stop,
  output logic stop_err
);

  always_ff @(posedge clk or posedge rst) begin
    if (rst) stop_err <= 1'b0;
    else if (check) stop_err <= (sampled_stop != 1'b1);
    else stop_err <= 1'b0;
  end

endmodule


//==================================================
// SIMPLE UART RX FSM (middle sampling, parameterized)
//==================================================
module rx_fsm_simple #(
  parameter int DATA_BITS = 8,
  parameter bit PARITY_EN = 1'b1,
  parameter int STOP_BITS = 1,
  parameter int BAUD_DIV = 10         // must match baud generator RX_DIV
)(
  input  logic clk,
  input  logic rst,
  input  logic start_detected,   // falling edge of start bit
  input  logic sample_tick,      // rx_enb (baud tick)
  input  logic rx_in,
  output logic shift,
  output logic parity_check,
  output logic stop_check,
  output logic data_ready
);

  typedef enum logic [3:0] {
    IDLE,
    MID_WAIT,     // wait half bit
    DATA_WAIT,    // wait full bit
    PARITY_WAIT,
    STOP_WAIT,
    DONE
  } state_t;

  state_t state;
  int unsigned bit_cnt;
  int unsigned stop_cnt;

  // compute half-bit (round down if odd)
  localparam int HALF_DIV = (BAUD_DIV/2 == 0) ? 1 : (BAUD_DIV/2);

  int half_cnt;

  // reset/initial values
  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      state <= IDLE;
      bit_cnt <= 0;
      stop_cnt <= 0;
      half_cnt <= 0;
      shift <= 1'b0;
      parity_check <= 1'b0;
      stop_check <= 1'b0;
      data_ready <= 1'b0;
    end
    else begin
      // defaults each cycle
      shift <= 1'b0;
      parity_check <= 1'b0;
      stop_check <= 1'b0;
      data_ready <= 1'b0;

      case (state)
        // ----- IDLE -----
        IDLE: begin
          bit_cnt <= 0;
          stop_cnt <= 0;
          half_cnt <= 0;
          if (start_detected) begin
            half_cnt <= 0;
            state <= MID_WAIT;
          end
        end

        // ----- Wait half bit to sample first data bit in the middle -----
        MID_WAIT: begin
          if (sample_tick) begin
            half_cnt <= half_cnt + 1;
            if (half_cnt == HALF_DIV-1) begin
              // sample first data bit (middle of bit0)
              shift <= 1'b1;
              bit_cnt <= 1;
              // prepare for subsequent full-bit waits
              state <= DATA_WAIT;
            end
          end
        end

        // ----- Wait full bit between samples; shift once each full period -----
        DATA_WAIT: begin
          if (sample_tick) begin
            if (bit_cnt < DATA_BITS) begin
              shift <= 1'b1;
              bit_cnt <= bit_cnt + 1;
            end

            // when we've sampled DATA_BITS bits, move to parity/stop next
            if (bit_cnt >= DATA_BITS) begin
              state <= PARITY_EN ? PARITY_WAIT : STOP_WAIT;
            end
          end
        end

        // ----- Parity sample once -----
        PARITY_WAIT: begin
          if (sample_tick) begin
            parity_check <= 1'b1;
            state <= STOP_WAIT;
          end
        end

        // ----- Stop bit(s) sample -----
        STOP_WAIT: begin
          if (sample_tick) begin
            stop_check <= 1'b1;
            stop_cnt <= stop_cnt + 1;
            if (stop_cnt + 1 >= STOP_BITS) begin
              // we've sampled required number of stop bits
              stop_cnt <= 0;
              state <= DONE;
            end
          end
        end

        // ----- Done, indicate ready then go idle -----
        DONE: begin
          data_ready <= 1'b1;
          bit_cnt <= 0;
          half_cnt <= 0;
          state <= IDLE;
        end

        default: state <= IDLE;
      endcase
    end
  end

endmodule
