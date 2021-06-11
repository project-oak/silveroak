module nestedloop_tb ();

  timeunit 1ns; timeprecision 1ns;

  logic clk;
  logic rst;

  int unsigned o;

  nestedloop nestedloop_inst (.clk(clk), .rst(rst), .o(o));

  initial begin
  $dumpfile("nestedloop_tb.vcd");
  $dumpvars(0, nestedloop_tb);
  clk <= 1'b0 ;
  rst <= 1'b1;
  #10 rst <= 1'b0;
  #900 $finish;
  end

  always #5 clk = !clk;

endmodule