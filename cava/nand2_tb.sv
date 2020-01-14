//
// Copyright 2019 The Project Oak Authors
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

module nand2_test;
  
  timeunit 1ns; timeprecision 1ns;

  logic a, b, c;
  logic rst;
  logic clk;
  
  nand2 nand2_dut  (.*);

  initial begin
    clk <= 0;
    forever #5 clk = ~clk;
  end
 
  initial $monitor($time, "a = %b, b = %b, c = %b", a, b, c);

  initial begin
    assign a = 1'b0;
    assign b = 1'b0;
    assign rst = 1'b1;
    @(posedge clk);
    @(posedge clk);
    assign rst = 1'b0;
    @(posedge clk);
    assign a = 1'b1;
    assign b = 1'b0;
    @(posedge clk);
    assign a = 1'b0;
    assign b = 1'b1;
    @(posedge clk);
    assign a = 1'b1;
    assign b = 1'b1;
    @(posedge clk);
    assign a = 1'b0;
    assign b = 1'b0;
    @(posedge clk);
    @(negedge clk) $finish;
  end
  
  initial
  begin
    $dumpfile("nand2.vcd");
    $dumpvars;
   end

endmodule