class uart_monitor;
  virtual uart_if vif;
  mailbox mon2sb;
  uart_transaction tr;

  function new(virtual uart_if vif, mailbox mon2sb);
    this.vif = vif;
    this.mon2sb = mon2sb;
  endfunction

  task run();
    forever begin
      @(posedge vif.clk);
      if (vif.cb.data_ready) begin
        tr = new();
        tr.data  = vif.cb.RX_data_out;
        tr.start = vif.cb.TXstart;
        tr.sample_coverage();      // sample only on valid data
        mon2sb.put(tr);
        tr.display("MON: Received");
      end
    end
  endtask
endclass
