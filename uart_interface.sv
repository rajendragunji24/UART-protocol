interface uart_if (input logic clk, input logic rst);

  //==================================================
  // 1. Signal Declarations
  //==================================================
  logic        TXstart;
  logic [7:0]  TX_data_in;
  logic        TX_data_out;
  logic        TX_busy;

  logic        RX_in;
  logic [7:0]  RX_data_out;
  logic        data_ready;
  logic        parity_err;
  logic        stop_err;

  //==================================================
  // 2. Clocking Block
  //==================================================
  clocking cb @(posedge clk);
    output TXstart, TX_data_in;
    input  TX_data_out, TX_busy;
    input  RX_data_out, data_ready, parity_err, stop_err;
  endclocking


  //==================================================
  // 3. Assertions Section
  //==================================================

  //----------------------------------------------
  // A. TXstart must not occur when TX_busy = 1
  // (Allowed only if TX_busy clears within 1–2 cycles)
  //----------------------------------------------
  property txstart_overlap_allowed;
    @(posedge clk) disable iff (rst)
      TXstart |-> (!TX_busy or ##[1:2] !TX_busy);
  endproperty

  assert property (txstart_overlap_allowed)
    else $warning("WARNING: TXstart asserted while TX_busy is high!");


  //----------------------------------------------
  // B. Data must remain stable for 2 cycles when data_ready=1
  //----------------------------------------------
  property data_stable_on_ready;
    @(posedge clk) disable iff (rst)
      data_ready |-> $stable(RX_data_out)[*2];
  endproperty

  assert property (data_stable_on_ready)
    else $error("ASSERTION FAILED: RX_data_out changed when data_ready=1!");


  //----------------------------------------------
  // C. Parity error and Stop error must never happen together
  //----------------------------------------------
  property no_parity_and_stop_err_together;
    @(posedge clk) disable iff (rst)
      !(parity_err && stop_err);
  endproperty

  assert property (no_parity_and_stop_err_together)
    else $error("ASSERTION FAILED: parity_err and stop_err both high!");


  //----------------------------------------------
  // D. After TXstart, data_ready must come within UART frame time
  // (Simulation-friendly bound)
  //----------------------------------------------
  property data_ready_after_txstart;
    @(posedge clk) disable iff (rst)
      TXstart |-> ##[5:50000] data_ready;
  endproperty

  assert property (data_ready_after_txstart)
    else $warning("WARNING: Data not ready within expected UART cycles after TXstart!");


  //----------------------------------------------
  // E. Display informational message on valid reception
  //----------------------------------------------
  always @(posedge clk)
    if (data_ready)
      $display("INFO: Data ready, RX_data_out = %0h", RX_data_out);

endinterface
