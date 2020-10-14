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

# This Makefile by default builds all targets that are part of the
# Silver Oak system except those that require the invocation of the
# Xilinx tools for simulation or FPGA implementation.

# Build everything (except Xilinx-specific targets):
# make

# Clean everything:
# make clean

.PHONY: all third_party cava tests monad-examples \
	arrow-examples silveroak-opentitan clean

all:	third_party cava tests monad-examples \
	arrow-examples silveroak-opentitan

# Third party dependencies should be built first.
third_party:
	cd third_party && $(MAKE)

# The cava targert builds the core Cava DSL.
cava:
	cd cava && $(MAKE)

# The cava target runs the unit tests for the Cava DSL
tests:
	cd tests/xilinx && $(MAKE) extraction

# The monad-example builds and tests the monad examples (except for
# the Xilinx-specific targets)
monad-examples:
	cd monad-examples && $(MAKE)

# The arrow-example builds and tests the arrow examples (except for
# the Xilinx-specific targets)
arrow-examples:
	cd arrow-examples && $(MAKE)

# The silveroak-opentitan builds the targets developed for the
# Silver Oak re-implementation of some OpenTitan blocks.
silveroak-opentitan:
	cd silveroak-opentitan && $(MAKE)
clean:
	cd third_party && $(MAKE) clean
	cd cava && $(MAKE) clean
	cd tests/xilinx && $(MAKE) clean
	cd monad-examples && $(MAKE) clean
	cd arrow-examples && $(MAKE) clean
	cd silveroak-opentitan && $(MAKE) clean
