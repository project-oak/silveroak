# LED Counter Test Example for the ZCU104 Xilinx FPGA Board

This directory contains a simple example that makes the four user GPIO LEDs on the ZCU104 board count in a binary pattern from 0 to 15 at a frequency of 1Hz. The design uses the 125MHZ differential clock input and divides it down to a 1Hz clock used to increment a count register. The output of the count register drives the four user LEDs.

The design can be loaded in Vivado or the bitstream can be generated using the `Makefile`:
```
$ make leds.bit
```
The FPGA can also be programming from the `Makefile`:
```
$ make configure
```
