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

module adder_tree4_8_test;
  
  timeunit 1ns; timeprecision 1ns;

  logic [7:0] a, b, c, d;
  logic [7:0] sum;
  
  adder_tree4_8 adder_tree4_8_inst  (.*);
 
  initial $monitor($time, " a = %0d, b = %0d,  c = %0d, d = %0d, sum = %0d", 
                   a, b, c, d, sum);

  initial begin
    assign a   = 8'd4;
    assign b   = 8'd5;
    assign c   = 8'd11;
    assign d   = 8'd9;
    #10
    assign a   = 8'd15;
    assign b   = 8'd3;
    assign c   = 8'd200;
    assign d   = 8'd7;
    #10
    $finish;
  end
  
  initial
  begin
    $dumpfile("adder_tree4_8.vcd");
    $dumpvars;
  end

endmodule
