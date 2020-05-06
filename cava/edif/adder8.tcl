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
file mkdir $outputDir
read_verilog adder8.sv
synth_design -mode out_of_context  -top adder8 -part xc7a200tsbg484-1
write_edif -force adder8.edn
exit
