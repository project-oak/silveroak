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

module add4(
  input logic[3:0] a,
  input logic[3:0] b,
  output logic[3:0] c
);

  assign c = a + b;

endmodule

module indexing(
  input logic clk
);

  timeunit 1ns; timeprecision 1ns;

  logic[7:0] wombat = 8'b10011100;
  logic[2:0] iv = 3'd7;
  logic bat1 = wombat[7];
  logic bat2 = wombat[iv];
  logic[2:0] sel = '{1'b1, 1'b1, 1'b1};
  logic bat3 = wombat[sel];

  logic[3:0] sum1;
  logic[3:0] sum2;
  logic[3:0] sum3;
  logic[3:0] sum4;
  logic[3:0] sum5;
  logic[3:0] sums[2];

  add4 av1 (.a(4'b0010), .b(4'b1100), .c(sum1));
  add4 av2 (.a({1'b0, 1'b0, 1'b1, 1'b0}), .b(4'b1100), .c(sum2));

  logic x[4] = '{1'b0, 1'b0, 1'b1, 1'b0};
  logic y[4] = '{1'b1, 1'b0, 1'b0, 1'b0};

  assign sum3 = {1'b0, 1'b0, 1'b1, 1'b0} + 'b1100;

  assign sum4 = {1'b0, 1'b0, 1'b1, 1'b0} + 4'b1100;

  assign sum5 = {x[0], x[1], x[2], x[3]} + 4'b1100;

  logic[3:0] p = {1'b0, 1'b0, 1'b1, 1'b0};
  logic[3:0] q = 4'b1100;

  assign sums = '{p, q};

  logic i1 = 1'b1;
  logic i0 = 1'b0;
  logic sel1 = 1'b1;
  logic o;

  logic[1:0] v0;
  logic[0:0] v1;

  assign o = v0[v1];
  assign v1 = {sel1};
  assign v0 = {i1,i0};


  initial begin
    $display("bat1 = %b", bat1);
    $display("bat2 = %b", bat2);
    $display("bat3 = %b", bat3);
    $display("sum1 = %d", sum1);
    $display("sum2 = %d", sum2);
    $display("sum3 = %d", sum3);
    $display("sum3 = %d", sum4);
    $display("sum5 = %d", sum5);
    $display("sums = %d %d", sums[0], sums[1]);
    $display("v0 = %x", v0);
    $display("v1 = %x", v1);
    $display("o = %b", o);
  end

endmodule  