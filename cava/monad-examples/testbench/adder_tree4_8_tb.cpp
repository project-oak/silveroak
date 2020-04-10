/*
 * Copyright 2020 The Project Oak Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <stdlib.h>
#include "Vadder_tree4_8_tb.h"
#include "verilated.h"
#include "verilated_vpi.h"
#include "verilated_vcd_c.h" 

double main_time = 0;
double sc_time_stamp() { return main_time; }

int main(int argc, char **argv) {
	Verilated::commandArgs(argc, argv);

	Vadder_tree4_8_tb *top = new Vadder_tree4_8_tb;

    VerilatedVcdC* vcd_trace = new VerilatedVcdC;

    Verilated::traceEverOn(true);
    top->trace(vcd_trace, 99);
    vcd_trace->open("adder_tree4_8_tb.vcd");

    for (unsigned int i = 0; i < 2; i++) {
        top->clk = 0; main_time += 5;
        top->eval(); vcd_trace->dump(main_time);
        top->clk = 1;  main_time += 5;
        top->eval(); vcd_trace->dump(main_time);
    }
    vcd_trace->close();
    delete top;
    exit(EXIT_SUCCESS);
}
