`timescale 1ns/1ps

//==================================================
// 1. BAUD RATE GENERATOR
//==================================================
module baud_rate_generator #(
  parameter int TX_DIV = 5208,  // Divider for transmitter
  parameter int RX_DIV = 5208   // Divider for receiver
)(
  input  logic clk,
  input  logic rst_n,           // Active-low reset
  output logic tx_enb,
  output logic rx_enb
);

  logic [12:0] tx_counter;
  logic [12:0]  rx_counter;

  // TX counter
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      tx_counter <= '0;
    else if (tx_counter == TX_DIV)
      tx_counter <= '0;
    else
      tx_counter <= tx_counter + 1'b1;
  end

  // RX counter
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      rx_counter <= '0;
    else if (rx_counter == RX_DIV)
      rx_counter <= '0;
    else
      rx_counter <= rx_counter + 1'b1;
  end

  assign tx_enb = (tx_counter == 0);
  assign rx_enb = (rx_counter == 0);

endmodule


//==================================================
// 2. PARITY GENERATOR
//==================================================
module parity_gen (
  input  logic [7:0] data_in,
  output logic       parity_bit
);
  always_comb parity_bit = ^data_in; // even parity
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
    if (rst)
      shift_reg <= 8'd0;
    else if (load)
      shift_reg <= data_in;
    else if (shift)
      shift_reg <= {1'b0, shift_reg[7:1]};
  end

  assign serial_out = shift_reg[0];
endmodule


//==================================================
// 4. TX FSM
//==================================================
module tx_fsm (
  input  logic clk,
  input  logic rst,
  input  logic TXstart,
  input  logic parity_bit,
  input  logic data_bit,
  output logic load,
  output logic shift,
  output logic [1:0] sel,   // 00=start, 01=data, 10=parity, 11=stop
  output logic TX_busy
);
  typedef enum logic [2:0] {
    IDLE, START, DATA, PARITY, STOP
  } state_t;

  state_t current_state, next_state;
  logic [2:0] bit_count;

  always_ff @(posedge clk or posedge rst)
    if (rst) current_state <= IDLE;
    else     current_state <= next_state;

  always_comb begin
    next_state = current_state;
    case (current_state)
      IDLE:   if (TXstart) next_state = START;
      START:  next_state = DATA;
      DATA:   if (bit_count == 3'd7) next_state = PARITY;
      PARITY: next_state = STOP;
      STOP:   next_state = IDLE;
    endcase
  end

  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      load <= 0; 
      shift <= 0; 
      sel <= 2'b00;
      TX_busy <= 0; 
      bit_count <= 0;
    end else begin
      load <= 0; 
      shift <= 0;
      case (current_state)
        IDLE: begin
          TX_busy <= 0;
          sel <= 2'b11;
          if (TXstart) begin load <= 1; TX_busy <= 1; end
        end
        START: sel <= 2'b00;
        DATA: begin sel <= 2'b01; 
          shift <= 1; 
          bit_count <= bit_count + 1; 
        end
        PARITY: sel <= 2'b10;
        STOP: begin sel <= 2'b11; TX_busy <= 0; 
           bit_count <= 0; 
        end
      endcase
    end
  end
endmodule


//==================================================
// 5. START BIT DETECTOR WITH SYNCHRONIZER
//==================================================
module start_bit_detect_sync (
  input  logic clk,
  input  logic rst,
  input  logic RX_in,
  output logic start_detected
);
  logic rx_sync0, rx_sync1, rx_prev;

  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin rx_sync0 <= 1; rx_sync1 <= 1; end
    else begin rx_sync0 <= RX_in; rx_sync1 <= rx_sync0; end
  end

  always_ff @(posedge clk or posedge rst)
    if (rst) rx_prev <= 1;
    else     rx_prev <= rx_sync1;

  always_ff @(posedge clk or posedge rst)
    if (rst) start_detected <= 0;
    else if (rx_prev && ~rx_sync1) start_detected <= 1;
    else start_detected <= 0;
endmodule


//==================================================
// 6. SIPO (Serial-In Parallel-Out)
//==================================================
module sipo_simple #(
  parameter int WIDTH = 8
) (
  input  logic clk,
  input  logic rst,
  input  logic shift,
  input  logic sampled_bit,
  output logic [WIDTH-1:0] data_out
);
  always_ff @(posedge clk or posedge rst)
    if (rst) data_out <= '0;
    else if (shift) data_out <= {sampled_bit, data_out[WIDTH-1:1]};
endmodule


//==================================================
// 7. PARITY CHECK
//==================================================
module parity_check_simple #(
  parameter int WIDTH = 8,
  parameter bit ODD_PARITY = 1'b0
) (
  input  logic clk,
  input  logic rst,
  input  logic check,
  input  logic [WIDTH-1:0] data_in,
  input  logic sampled_parity,
  output logic parity_err
);
  logic parity_xor;
  always_comb parity_xor = ^data_in;

  always_ff @(posedge clk or posedge rst)
    if (rst) parity_err <= 0;
    else if (check)
      parity_err <= (sampled_parity != (ODD_PARITY ? ~parity_xor : parity_xor));
    else parity_err <= 0;
endmodule


//==================================================
// 8. STOP BIT CHECK
//==================================================
module stop_check_simple (
  input  logic clk,
  input  logic rst,
  input  logic check,
  input  logic sampled_stop,
  output logic stop_err
);
  always_ff @(posedge clk or posedge rst)
    if (rst) stop_err <= 0;
    else if (check) stop_err <= (sampled_stop != 1);
    else stop_err <= 0;
endmodule


//==================================================
// 9. RX FSM
//==================================================
module rx_fsm_simple #(
  parameter int DATA_BITS = 8,
  parameter bit PARITY_EN = 1'b0,
  parameter int STOP_BITS = 1
) (
  input  logic clk,
  input  logic rst,
  input  logic start_detected,
  input  logic sample_tick,
  input  logic rx_in,
  output logic shift,
  output logic parity_check,
  output logic stop_check,
  output logic data_ready
);
  typedef enum logic [2:0] {IDLE, WAIT_FIRST, DATA, PARITY, STOP, DONE} state_t;
  state_t state;
  int unsigned bit_cnt, stop_cnt;

  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      state <= IDLE; 
      bit_cnt <= 0; 
      stop_cnt <= 0;
      shift <= 0; 
      parity_check <= 0; 
      stop_check <= 0; 
      data_ready <= 0;
    end else begin
      shift <= 0; 
      parity_check <= 0; 
      stop_check <= 0; 
      data_ready <= 0;
      case (state)
        IDLE: if (start_detected) 
          state <= WAIT_FIRST;
        WAIT_FIRST: if (sample_tick) begin 
          shift <= 1; 
          bit_cnt <= 1;
          state <= (DATA_BITS==1)?(PARITY_EN?PARITY:STOP):DATA; 
        end
        DATA: if (sample_tick) begin 
          shift <= 1; 
          bit_cnt++;
          if (bit_cnt==DATA_BITS) 
            state <= PARITY_EN?PARITY:STOP; 
        end
        PARITY: if (sample_tick) begin 
          parity_check <= 1; 
          state <= STOP; 
        end
        STOP: if (sample_tick) begin 
          stop_check <= 1; 
          stop_cnt++;
          if (stop_cnt>=STOP_BITS) 
            state <= DONE;
        end
        DONE: begin data_ready <= 1; 
          bit_cnt <= 0; 
          stop_cnt <= 0; 
          state <= IDLE; 
        end
      endcase
    end
  end
endmodule
