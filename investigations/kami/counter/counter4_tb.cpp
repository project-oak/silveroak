/*
 * Copyright 2019 The Project Oak Authors
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
#include "VmkModule1.h"
#include "verilated.h"
#include "verilated_vcd_c.h" 

int main(int argc, char **argv) {
	Verilated::commandArgs(argc, argv);

	VmkModule1 *counter4 = new VmkModule1;

    VerilatedVcdC* vcd_trace = new VerilatedVcdC;

    Verilated::traceEverOn(true);
    counter4->trace(vcd_trace, 99);
    vcd_trace->open("counter4_tb.vcd");

    vluint64_t time = 0;

    counter4->CLK = 0;
    counter4->RST_N = 0;
    counter4->EN_count_value = 1;
    counter4->eval();
    vcd_trace->dump(time);

    counter4->CLK = 1;
    counter4->eval();
    time += 10;
    vcd_trace->dump(time);

    counter4->CLK = 0;
    counter4->RST_N = 1;
    time += 10;
    counter4->eval();
    vcd_trace->dump(time);

	for (int i = 1; i < 20; ++ i) {
		counter4->CLK = 1;
		counter4->eval();
        time += 10;
        vcd_trace->dump(time);
		counter4->CLK = 0;
		counter4->eval();
        time += 10;
        vcd_trace->dump(time);
	}
    vcd_trace->close();
    exit(EXIT_SUCCESS);
}
