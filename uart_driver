class uart_driver;
  virtual uart_if vif;
  mailbox gen2drv;

  function new(virtual uart_if vif, mailbox gen2drv);
    this.vif = vif;
    this.gen2drv = gen2drv;
  endfunction

  task run();
    uart_transaction tr;
    forever begin
      gen2drv.get(tr);
      @(posedge vif.clk);
      vif.cb.TX_data_in  <= tr.data;
      vif.cb.TXstart     <= tr.start;
      tr.display("DRV: Sent");
      @(posedge vif.clk);
      vif.cb.TXstart     <= 0; // deassert start
      wait(vif.cb.TX_busy == 0); // wait for transmission done
    end
  endtask
endclass
