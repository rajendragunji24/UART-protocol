class uart_generator;
  mailbox gen2drv;
  int num_tx = 50;

  function new(mailbox gen2drv);
    this.gen2drv = gen2drv;
  endfunction

  task run();
    uart_transaction tr;
    repeat (num_tx) begin
      tr = new();
      assert(tr.randomize() with {
        start == 1;  // always start transmission
      });
      tr.display("GEN");
      gen2drv.put(tr);
      #20;
    end
  endtask
endclass
