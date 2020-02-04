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

module fulladderFC_test;
  
  timeunit 1ns; timeprecision 1ns;

  logic a, b, cin, sum, carry;
  
  fulladderFC fulladderFC_inst  (.*);
 
  initial $monitor($time, " a = %b, b = %b, cin = %b, sum = %d, carry = %d",
                   a, b, cin, sum, carry);

  initial begin
    assign a   = 1'b0;
    assign b   = 1'b0;
    assign cin = 1'b0;
    #10
    assign a   = 1'b1;
    assign b   = 1'b0;
    assign cin = 1'b0;
    #10
    assign a   = 1'b1;
    assign b   = 1'b1;
    assign cin = 1'b0;
    #10
    assign a   = 1'b1;
    assign b   = 1'b1;
    assign cin = 1'b1;
    $finish;
  end
  
  initial
  begin
    $dumpfile("fulladderFC.vcd");
    $dumpvars;
  end

endmodule