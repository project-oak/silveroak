//
// Copyright 2020 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

module adder_tree4_8_tb(
   input logic clk
);
  
  timeunit 1ns; timeprecision 1ns;

  logic [7:0] a, b, c, d;
  logic [7:0] sum;

  adder_tree4_8 adder_tree4_8_inst  (.*);

  logic [7:0] test_vectors[2][4]
    = '{ '{ 8'd4,  8'd5, 8'd11,  8'd9 },
         '{ 8'd15, 8'd3, 8'd200, 8'd7 }
       };

  logic[7:0] expected_output[2] = '{ 8'd29, 8'd225 };     

  int unsigned i = 0;

  assign a = test_vectors[i][0];
  assign b = test_vectors[i][1];
  assign c = test_vectors[i][2];
  assign d = test_vectors[i][3]; 

  always @(posedge clk) begin
    $display ($time, " i = %0d, a = %0d, b = %0d, c = %0d, d = %0d, sum = %0d", i, a, b, c, d, sum);
    if (sum != expected_output[i]) begin
      $error("Expected %0d but got %0d", expected_output[i], sum);
    end;
    if (i == 1) begin
      $display ("PASSED");
      $finish;
    end else begin
      i <= i + 1 ;
    end;
  end

endmodule
