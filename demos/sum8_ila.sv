// Automatically generated SystemVerilog 2012 code from Cava
// Please do not hand edit.

module sum8_tb(
  input logic clk,
  input logic rst
);

  timeunit 1ns; timeprecision 1ns;


  sum8 sum8_inst (.*);

  // Circuit inputs
  (* mark_debug = "true" *) logic [7:0]i;
  // Circuit outputs
  (* mark_debug = "true" *) logic [7:0]o;
  // Input test vectors
  (* mark_debug = "true" *) logic [7:0]i_vectors[7] = '{
    8'd3, 
    8'd5, 
    8'd7, 
    8'd2, 
    8'd4, 
    8'd6,
    8'd0
    };

  int unsigned i_cava = 0;
  assign i = i_vectors[i_cava];

  always @(posedge clk) begin
    if (rst == 1'b1)
      i_cava = 0;
    else
      if (i_cava < 6) 
        i_cava <= i_cava + 1 ;
  end
endmodule
