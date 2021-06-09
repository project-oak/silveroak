module counter6_tb ();

  timeunit 1ns; timeprecision 1ns;

  logic clk;
  logic rst;

  int unsigned count6;

  counter6 counter6_inst (.clk(clk), .rst(rst), .count6(count6));

  initial begin
  $dumpfile("counter6_tb.vcd");
  $dumpvars(0, counter6_tb);
  clk <= 1'b0 ;
  rst <= 1'b1;
  #10 rst <= 1'b0;
  #900 $finish;
  end

  always #5 clk = !clk;

endmodule