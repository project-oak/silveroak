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

module adder8_3in_test;
  
  timeunit 1ns; timeprecision 1ns;

  logic cin, cout;
  logic [7:0] a, b, c;
  logic [9:0] sum;
  
  adder8_3in adder8__3in_inst  (.*);
 
  initial $monitor($time, " a = %0d, b = %0d, c = %0d, sum = %0d", a, b, c, sum);

  initial begin
    assign a   = 8'd4;
    assign b   = 8'd5;
    assign c   = 8'd11;
    #10
    assign a   = 8'd15;
    assign b   = 8'd3;
    assign c   = 8'd200;
    #10
    $finish;
  end
  
  initial
  begin
    $dumpfile("adder8_3in.vcd");
    $dumpvars;
  end

endmodule