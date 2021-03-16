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

.PHONY:	all minimize-requires coqutil coqtools bedrock2 extlib record-update \
	clean no-update update build-coqutil build-bedrock2 build-extlib \
	build-record-update clean coq

all: coqutil coqtools bedrock2 extlib record-update

update:
	git submodule update --init --recursive

no-update: build-coqutil build-bedrock2 build-extlib build-record-update

minimize-requires: # noop

build-coqutil:
	$(MAKE) -C bedrock2/deps/coqutil all

build-bedrock2: build-coqutil
	$(MAKE) -C bedrock2 bedrock2_noex

build-extlib:
	$(MAKE) -C coq-ext-lib theories

build-record-update:
	$(MAKE) -C coq-record-update

# coq-tools is just python scripts; nothing to build
coqtools: update

coqutil: update
	$(MAKE) build-coqutil

bedrock2: update
	$(MAKE) build-bedrock2

extlib: update
	$(MAKE) build-extlib

record-update: update
	$(MAKE) build-record-update

install: update
	cd bedrock2 && $(MAKE) install_coqutil && $(MAKE) install_bedrock2
	cd coq-ext-lib && $(MAKE) install

coq: all

clean:
	-cd bedrock2 && $(MAKE) clean_all
	-cd coq-ext-lib && $(MAKE) clean
