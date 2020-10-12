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

################################################################################
# This Makefile copies over and lints just the SystemVerilog files
# needed for the pinmux of OpenTitan.
################################################################################

OPENTITAN = ../../../third_party/opentitan

.PHONY:	all clean check_oldpinmux

all:	vlint

SOURCES = pinmux.vlt prim_assert.sv top_pkg.sv tlul_pkg.sv tlul_err.sv \
	  prim_subreg.sv prim_subreg_ext.sv tlul_adapter_reg.sv \
          pinmux_reg_pkg.sv pinmux_reg_top.sv prim_pulse_sync.sv \
          prim_filter.sv prim_flop_2sync.sv pinmux.sv

vlint:	$(SOURCES)
	verilator +1800-2012ext+sv -Wno-fatal --lint-only $^ --top-module pinmux

prim_assert.sv:	$(OPENTITAN)/hw/ip/prim/rtl/prim_assert.sv
		cp $^ $@

top_pkg.sv:	$(OPENTITAN)/hw/top_earlgrey/rtl/top_pkg.sv
		cp $^ $@

tlul_pkg.sv:	$(OPENTITAN)/hw/ip/tlul/rtl/tlul_pkg.sv
		cp $^ $@

tlul_err.sv:	$(OPENTITAN)/hw/ip/tlul/rtl/tlul_err.sv
		cp $^ $@

prim_subreg.sv:	$(OPENTITAN)/hw/ip/prim/rtl/prim_subreg.sv
		cp $^ $@

prim_subreg_ext.sv:	$(OPENTITAN)/hw/ip/prim/rtl/prim_subreg_ext.sv
			cp $^ $@
		
tlul_adapter_reg.sv:	$(OPENTITAN)/hw/ip/tlul/rtl/tlul_adapter_reg.sv
			cp $^ $@

pinmux.vlt:	$(OPENTITAN)/hw/ip/pinmux/lint/pinmux.vlt
		cp $^ $@

pinmux_reg_top.sv:	$(OPENTITAN)/hw/top_earlgrey/ip/pinmux/rtl/autogen/pinmux_reg_top.sv
			cp $^ $@

pinmux_reg_pkg.sv:	$(OPENTITAN)/hw/top_earlgrey/ip/pinmux/rtl/autogen/pinmux_reg_pkg.sv
			cp $^ $@

prim_filter.sv:		$(OPENTITAN)/hw/ip/prim/rtl/prim_filter.sv
			cp $^ $@

prim_pulse_sync.sv:	$(OPENTITAN)/hw/ip/prim/rtl/prim_pulse_sync.sv
			cp $^ $@

prim_flop_2sync.sv:	$(OPENTITAN)/hw/ip/prim/rtl/prim_flop_2sync.sv
			cp $^ $@

pinmux_wkup.sv:	$(OPENTITAN)/hw/ip/pinmux/rtl/pinmux_wkup.sv
		cp $^ $@

pinmux.sv:	$(OPENTITAN)/hw/ip/pinmux/rtl/pinmux.sv
		cp $^ $@

pinmux_pkg.sv:	$(OPENTITAN)/hw/ip/pinmux/rtl/pinmux_pkg.sv
		cp $^ $@

clean:		
		rm -rf $(SOURCES)
