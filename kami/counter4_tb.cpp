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