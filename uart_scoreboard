class uart_scoreboard;
  mailbox gen2drv;
  mailbox mon2sb;
  uart_transaction sent_q[$];

  function new(mailbox gen2drv, mailbox mon2sb);
    this.gen2drv = gen2drv;
    this.mon2sb  = mon2sb;
  endfunction

  task run();
    uart_transaction tx, rx;
    forever begin
      // Get transmitted data from generator (driver)
      if (gen2drv.num() > 0) begin
        gen2drv.peek(tx);
        sent_q.push_back(tx);
      end

      // Get received data from monitor
      if (mon2sb.num() > 0) begin
        mon2sb.get(rx);
        if (sent_q.size() > 0) begin
          tx = sent_q.pop_front();
          if (tx.data == rx.data)
            $display("[SCB] PASS: TX=%0h RX=%0h", tx.data, rx.data);
          else
            $display("[SCB] FAIL: TX=%0h RX=%0h", tx.data, rx.data);
        end
      end
      #5;
    end
  endtask
endclass
