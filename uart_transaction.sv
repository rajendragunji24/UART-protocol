class uart_transaction;
  rand bit [7:0] data;
  rand bit       start;

  // ---------------------------------------
  // ✅ Functional Coverage (only start = 1)
  // ---------------------------------------
  covergroup trans_cov;
    coverpoint data {
      bins data_0_63   = {[0:63]};
      bins data_64_127 = {[64:127]};
      bins data_128_191= {[128:191]};
      bins data_192_255= {[192:255]};
    }

    coverpoint start {
      bins start_1 = {1}; // only valid start
    }

    cross data, start;
  endgroup

  function new();
    trans_cov = new();
  endfunction

  function void sample_coverage();
    trans_cov.sample();
  endfunction

  // auto-sample after every randomize
  function void post_randomize();
    trans_cov.sample();
  endfunction

  function void display(string tag = "");
    $display("[%0s] Data=%0h | Start=%0b", tag, data, start);
  endfunction
endclass
