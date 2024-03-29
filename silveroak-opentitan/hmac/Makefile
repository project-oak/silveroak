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

SUBDIRS = Spec hw sw end2end

.PHONY: all coq minimize-requires clean subdirs $(SUBDIRS)

all: subdirs

subdirs: $(SUBDIRS)

$(SUBDIRS):
	$(MAKE) -C $@ $(SUBDIRTARGET)

coq: $(SUBDIRS)

minimize-requires: $(SUBDIRS)

clean: $(SUBDIRS)

# pass the 'coq' target down to subdirs
coq: SUBDIRTARGET=coq

# pass the 'minimize-requires' target down to subdirs
minimize-requires: SUBDIRTARGET=minimize-requires

# pass the 'clean' target down to subdirs
clean: SUBDIRTARGET=clean

# strip off the first subdir name, then call make on that subdir with the specified .vo target
# for example, "make X/Y/Foo.vo" will call "make -C X Y/Foo.vo"
%.vo:
	$(MAKE) -C $(DIR) $(TARGET)

%.vo: DIR=$(firstword $(subst /, , $@))

%.vo: TARGET=$(subst $(DIR)/,,$@)

# hw depends on spec
hw: Spec

# sw depends on spec
sw: Spec

# end2end depends on hw, sw, and Spec
end2end: Spec hw sw
