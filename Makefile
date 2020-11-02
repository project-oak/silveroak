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

SUBDIRS = third_party cava tests monad-examples arrow-examples silveroak-opentitan monad-examples/xilinx tests/xilinx

.PHONY: all coq clean subdirs $(SUBDIRS)

# if the "make clean" or "make coq" targets were called, pass these to subdirs
ifeq ($(MAKECMDGOALS), coq)
SUBDIRTARGET="coq"
else ifeq ($(MAKECMDGOALS), clean)
SUBDIRTARGET="clean"
endif

all: subdirs

subdirs: $(SUBDIRS)

$(SUBDIRS):
	$(MAKE) -C $@ $(SUBDIRTARGET)

coq: $(SUBDIRS)

clean: $(SUBDIRS)

# cava depends on third_party
cava : third_party

# tests depends on cava
tests: cava

# tests/xilinx depends on tests
tests/xilinx : cava tests

# monad-examples depends on cava
monad-examples : cava

# monad-examples/xilinx depends on monad-examples
monad-examples/xilinx : monad-examples

# arrow-examples depends on cava
arrow-examples: cava

# silveroak-opentitan depends on cava
silveroak-opentitan : cava
