module pipe2_tb ();

  timeunit 1ns; timeprecision 1ns;

  logic clk;
  logic rst;

  int unsigned a, a2;

  pipe2 pipe2_inst (.clk(clk), .rst(rst), .a(a), .a2(a2));

  initial begin
  $dumpfile("pipe2_tb.vcd");
  $dumpvars(0, pipe2_tb);
  clk <= 1'b0 ;
  rst <= 1'b1;
  #10 rst <= 1'b0;
  #5  a <= 17;
  #10 a <= 92;
  #10 a <= 51;
  #20;
  $finish;
  end

  always #5 clk = !clk;

endmodule