################################################################################
# Generate the programming bit-stream for the counting LED example from the
# VHDL source and constraints file for the ZCU104 FPGA board.
################################################################################
leds.bit:	leds.vhd leds.xdc
			vivado -mode tcl -source leds.tcl

configure:	leds.bit
			vivado -mode tcl -source configure.tcl

clean:		
			rm -rf Leds_Created_Data leds.bit
