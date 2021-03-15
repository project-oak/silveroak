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
# Silver Oak system except documentation and those targets that require the
# invocation of the Xilinx tools for simulation or FPGA implementation.

# Build everything (except Xilinx-specific targets):
# make

# Clean everything:
# make clean

SUBDIRS = third_party cava tests examples silveroak-opentitan \
	  examples/xilinx tests/xilinx demos

.PHONY: all coq minimize-requires clean subdirs $(SUBDIRS)

all: subdirs

subdirs: $(SUBDIRS)

$(SUBDIRS):
	$(MAKE) -C $@ $(SUBDIRTARGET)

coq: $(SUBDIRS)

minimize-requires: $(SUBDIRS)

# clean everything *except for* third_party
clean:
	for dir in $(filter-out third_party,$(SUBDIRS)); do \
		$(MAKE) -C $$dir clean; \
	done

# clean everything *including* third_party
cleanall:
	for dir in $(SUBDIRS); do \
		$(MAKE) -C $$dir clean; \
	done

# pass the 'coq' target down to subdirs
coq: SUBDIRTARGET=coq

# pass the 'minimize-requires' target down to subdirs
minimize-requires: SUBDIRTARGET=minimize-requires

# strip off the first subdir name, then call make on that subdir with the specified .vo target
# for example, "make cava/X/Y/Foo.vo" will call "make -C cava X/Y/Foo.vo"
%.vo:
	$(MAKE) -C $(DIR) $(TARGET)

%.vo: DIR=$(firstword $(subst /, , $@))

%.vo: TARGET=$(subst $(DIR)/,,$@)


# cava depends on third_party
cava : third_party

# tests depends on cava
tests: cava

# tests/xilinx depends on tests
tests/xilinx : cava tests

# examples depends on cava
examples : cava

# demos depends on cava
demos : cava

# examples/xilinx depends on examples
examples/xilinx : examples

# silveroak-opentitan depends on cava
silveroak-opentitan : cava
