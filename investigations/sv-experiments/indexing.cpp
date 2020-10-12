#include <stdlib.h>
#include "Vindexing.h"
#include "verilated.h"
#include "verilated_vpi.h"
#include "verilated_vcd_c.h"

double main_time = 0;
double sc_time_stamp() { return main_time; }

int main(int argc, char **argv) {
  Verilated::commandArgs(argc, argv);
  Vindexing *top = new Vindexing;
  VerilatedVcdC* vcd_trace = new VerilatedVcdC;
  Verilated::traceEverOn(true);
  top->trace(vcd_trace, 99);
  top->eval(); vcd_trace->dump(main_time);
  vcd_trace->open("nand2_tb.vcd");
  for (unsigned int i = 0; i < 4; i++) {
    top->clk = 0; main_time += 5;
    top->eval(); vcd_trace->dump(main_time);
    top->clk = 1;  main_time += 5;
    top->eval(); vcd_trace->dump(main_time);
  }
  vcd_trace->close();
  delete top;
  exit(EXIT_SUCCESS);
}
