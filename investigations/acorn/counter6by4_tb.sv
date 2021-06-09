module counter6by4_tb ();

  timeunit 1ns; timeprecision 1ns;

  logic clk;
  logic rst;

  int unsigned count6by4;

  counter6by4 counter6_inst (.clk(clk), .rst(rst), .count6by4(count6by4));

  initial begin
  $dumpfile("counter6by4_tb.vcd");
  $dumpvars(0, counter6by4_tb);
  clk <= 1'b0 ;
  rst <= 1'b1;
  #10 rst <= 1'b0;
  #900 $finish;
  end

  always #5 clk = !clk;

endmodule