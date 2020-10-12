#
# Copyright 202 0The Project Oak Authors
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

.PHONY: compile xcompile clean

VERILATOR = verilator +1800-2012ext+sv
VLINT = $(VERILATOR) --lint-only


all:	
	$(VERILATOR) --trace --cc --top-module indexing indexing.sv --exe indexing.cpp indexing.cpp
	make -C obj_dir -f Vindexing.mk Vindexing
	obj_dir/Vindexing

xcompile:
		xvlog -sv uadd1.sv
		xelab work.uadd1 -s uadd1_sim
		xsim --R uadd1_sim

compile:
		iverilog -g2012 uadd1.sv


clean:		
		rm -rf a.out *.jou *.log *.pb xsim.dir 
		rm -rf obj_dir
