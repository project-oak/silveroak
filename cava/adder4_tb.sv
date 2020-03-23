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

module adder4_test;
  
  timeunit 1ns; timeprecision 1ns;

  logic cin, cout;
  logic [3:0] a, b;
  logic [4:0] sum;
  
  adder4 adder4_inst  (.*);
 
  initial $monitor($time, " a = %0d, b = %0d, sum = %0d", a, b, sum);

  initial begin
    assign a   = 4'd4;
    assign b   = 4'd5;
    #10
    assign a   = 4'd15;
    assign b   = 4'd3;
    #10
    $finish;
  end
  
  initial
  begin
    $dumpfile("adder4.vcd");
    $dumpvars;
  end

endmodule