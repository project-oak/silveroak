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

module uadd1;

  timeunit 1ns; timeprecision 1ns;

  logic a0, a1, a2;
  logic b0, b1, b2;
  logic c0, c1, c2;
  logic[2:0] ax, bx, cx; 

  initial begin
    assign a0 = 1'b0;
    assign a1 = 1'b1;
    assign a2 = 1'b0;
    assign b0 = 1'b0;
    assign b1 = 1'b0;
    assign b2 = 1'b1;
    assign ax = '{a0, a1, a2};
    assign bx = '{b0, b1, b2};
    assign cx = ax + bx;
    assign c0 = cx[0];
    assign c1 = cx[1];
    assign c2 = cx[2];
    $display("c = %d", cx);
  end

endmodule  