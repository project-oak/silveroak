# Vivado tcl script to synthesize, implement and generate write_bitstream
# for led counter example for the ZCU104 board.
# Usage: "vivado -mode tcl -source leds.tcl"
#
set outputDir ./Leds_Created_Data/leds_output
file mkdir $outputDir
#
read_vhdl leds.vhdl
read_xdc leds.xdc
#
synth_design -top leds -part xczu7ev-ffvc1156-2-e
write_checkpoint -force $outputDir/post_synth
report_timing_summary -file $outputDir/post_synth_timing_summary.rpt
report_power -file $outputDir/post_synth_power.rpt
#
opt_design
place_design
phys_opt_design
write_checkpoint -force $outputDir/post_place
report_timing_summary -file $outputDir/post_place_timing_summary.rpt
#
route_design
write_checkpoint -force $outputDir/post_route
report_timing_summary -file $outputDir/post_route_timing_summary.rpt
report_timing -sort_by group -max_paths 100 -path_type summary -file $outputDir/post_route_timing.rpt
report_clock_utilization -file $outputDir/clock_util.rpt
report_utilization -file $outputDir/post_route_util.rpt
report_power -file $outputDir/post_route_power.rpt
report_drc -file $outputDir/post_imp_drc.rpt
write_verilog -force $outputDir/leds_impl_netlist.v
write_xdc -no_fixed_only -force $outputDir/leds_impl.xdc
#
write_bitstream -force leds.bit
exit
