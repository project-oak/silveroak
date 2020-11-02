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

.PHONY:	all

all: coqutil bedrock2 extlib

update:
	git submodule update --init --recursive

coqutil: update
	$(MAKE) -C bedrock2/deps/coqutil all

bedrock2: update coqutil
	$(MAKE) -C bedrock2 bedrock2_noex

extlib: update
	$(MAKE) -C coq-ext-lib theories

install: update
	cd bedrock2 && $(MAKE) install_coqutil && $(MAKE) install_bedrock2
	cd coq-ext-lib && $(MAKE) install

coq: all

clean:
	-cd bedrock2 && $(MAKE) clean_all
	-cd coq-ext-lib && $(MAKE) clean
