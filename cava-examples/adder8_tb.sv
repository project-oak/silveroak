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

module adder_test;
  
  timeunit 1ns; timeprecision 1ns;

  logic cin, cout;
  logic [7:0] a, b, sum;
  
  adder8 adder8_inst  (.*);
 
  initial $monitor($time, " a = %0d, b = %0d, cin = %b, sum = %0d, cout = %d",
                   a, b, cin, sum, cout);

  initial begin
    assign a   = 8'd4;
    assign b   = 8'd17;
    assign cin = 1'b0;
    #10
    assign a   = 8'd7;
    assign b   = 8'd20;
    assign cin = 1'b0;
    #10
    assign a   = 8'd51;
    assign b   = 8'd62;
    assign cin = 1'b0;
    #10
    assign a   = 8'd200;
    assign b   = 8'd55;
    assign cin = 1'b1;
    $finish;
  end
  
  initial
  begin
    $dumpfile("adder8.vcd");
    $dumpvars;
  end

endmodule