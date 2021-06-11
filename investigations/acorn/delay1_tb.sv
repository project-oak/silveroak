module delay1_tb ();

  timeunit 1ns; timeprecision 1ns;

  logic clk;
  logic rst;

  int unsigned a, a1;

  delay1 delay_inst (.clk(clk), .rst(rst), .a(a), .a1(a1));

  initial begin
  $dumpfile("delay1_tb.vcd");
  $dumpvars(0, delay1_tb);
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