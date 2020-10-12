# LED Counter Test Example for the ZCU104 Xilinx FPGA Board

This directory contains a simple example that makes the four user GPIO LEDs on the [ZCU104](https://www.xilinx.com/products/boards-and-kits/zcu104.htm) board count in a binary pattern from 0 to 7 at a frequency of 1Hz. The design uses the 125MHZ differential clock input and divides it down to a 1Hz clock used to increment a count register. The output of the count register drives the four user LEDs.

The purpose of this design is to provide a baseline reference design that is used as the basis for other related Oak hardware examples that run on the ZCU104 FPGA board. 

The design can be loaded in Vivado or the bitstream can be generated using the `Makefile`:
```
$ make leds.bit
```
The FPGA can also be programming from the `Makefile`:
```
$ make configure
```
The four user LEDs should now blink in a 0..15 pattern and the execution of the circuit can be reset by pressing the SW18 push-button (top-left button). This picture shows some of the GPIO LEDs on which are
at the top-left hand corner of the board.
![ZCU104 FPGA board](zcu104.jpg)
