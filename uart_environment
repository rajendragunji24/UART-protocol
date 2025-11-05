`include "transaction.sv"
`include "generator.sv"
`include "driver.sv"
`include "monitor.sv"
`include "scoreboard.sv"

class uart_env;
  uart_generator  gen;
  uart_driver     drv;
  uart_monitor    mon;
  uart_scoreboard sb;

  mailbox gen2drv;
  mailbox mon2sb;
  mailbox gen2sb;

  virtual uart_if vif;

  function new(virtual uart_if vif);
    this.vif = vif;
    gen2drv = new();
    mon2sb  = new();
    gen2sb  = new();
    gen = new(gen2drv);
    drv = new(vif, gen2drv);
    mon = new(vif, mon2sb);
    sb  = new(mon2sb, gen2drv);
  endfunction

  task run();
    fork
      gen.run();
      drv.run();
      mon.run();
      sb.run();
    join_none
  endtask
endclass
