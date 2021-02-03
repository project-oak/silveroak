#
# Copyright 2021 The Project Oak Authors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

# This tcl script drives FPGA implementation far enough
# to get a post-placement utilization report. Give the
# root name of the module as the sole argument e.g.
# vivado -mode tcl -source aes_util.tcl -tclargs aes_sub_bytes

puts "Utilization report for [lindex $argv 0]"
set circuit [lindex $argv 0]
set outputDir ./aes_implementation/$circuit
file mkdir $outputDir
#
read_verilog -sv $circuit.sv
#
synth_design -top $circuit -part xc7a200tsbg484-1
write_checkpoint -force $outputDir/post_synth
report_utilization -file $outputDir/post_synth_util.rpt
opt_design
place_design
phys_opt_design
write_checkpoint -force $outputDir/post_place
report_utilization -file $outputDir/post_route_util.rpt
report_timing_summary -file $outputDir/post_place_timing_summary.rpt
#
route_design
write_checkpoint -force $outputDir/post_route
report_timing_summary -file $outputDir/post_route_timing_summary.rpt
report_timing -sort_by group -max_paths 100 -path_type summary -file $outputDir/post_route_timing.rpt
report_clock_utilization -file $outputDir/clock_util.rpt
report_utilization -file $outputDir/post_route_util.rpt
exit
