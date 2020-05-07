#
# Copyright 2020 The Project Oak Authors
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

# Vivado tcl script to synthesize, implement and generate write_bitstream
# for the add8.sv example for EDIF extraction
#
set outputDir ./vivado_genfiles/output
create_project -force lutNAND lutNAND -part xc7A200tsbg484-1
add_files -fileset sim_1 -norecurse lutNAND_tb.sv lutNAND.sv 
set_property top lutNAND_tb  [get_filesets sim_1]
import_files -force -norecurse
launch_simulation
open_vcd lutNAND_tb.vcd
log_vcd *
log_vcd [ get_objects *]
add_force {/lutNAND_tb/clk} {0 0ns} {1 50ns} -repeat_every 100ns
run 400ns
flush_vcd
close_vcd
exit
