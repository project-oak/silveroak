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

module loopedNAND_test;
  
  timeunit 1ns; timeprecision 1ns;

  logic clk, rst, a, b, c;
  
  loopedNAND loopedNAND_inst  (.*);

  initial begin 
    clk = 1'b1; 
  end 

  // Clock generation.
  always #5 clk = ~clk;

  always @(posedge clk) $display($time, " a = %0b, b = %0b", a, b);

  // Synchronous reset generation
  initial begin
    rst = 1'b1;
    #10 rst = 1'b0;
  end

  initial begin
    assign a   = 1'b0; // a = 0, reg out = 0, gate out = 1
    @(posedge clk);
    assign a   = 1'b0; // a = 0, reg out = 1, gate out = 1
    @(posedge clk);
    assign a   = 1'b1; // a = 1, reg out = 1, gate out = 0
    @(posedge clk);
    assign a   = 1'b1; // a = 1, reg out = 0, gate out = 1
    @(posedge clk);
    assign a   = 1'b1; // a = 1, reg out = 1, gate out = 0 FLIP
    @(posedge clk);
    assign a   = 1'b1; // a = 1, reg out = 0, gate out = 1 FLIP
    @(posedge clk);
    assign a   = 1'b0; // a = 0, reg out = 1, gate out = 1 FORCE-1
    @(posedge clk);
    assign a   = 1'b0; // a = 0, reg out = 1, gate out = 1 FORCE-1
    @(posedge clk);
    assign a   = 1'b0; // FORCE state to 1
    @(posedge clk);
    assign a   = 1'b1; // FLIP state to 0
    @(posedge clk);
    assign a   = 1'b1; // FLIP state to 1
    @(posedge clk);
    assign a   = 1'b1; // FLIP state to 0
    @(posedge clk);
    $finish;
  end
  
  initial
  begin
    $dumpfile("loopedNAND.vcd");
    $dumpvars;
  end

endmodule