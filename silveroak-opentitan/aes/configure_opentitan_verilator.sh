#!/bin/bash

#
# Copyright 2021 The Project Oak Authors
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

VERILATOR_CONFIG=../../third_party/opentitan/hw/lint/tools/verilator/common.vlt

# OpenTitan Verilator config is empty, we need to turn off "DETECTARRAYS" as we
# generate large arrays that choke Verilator. Alternatively we could
# rebuild Verilator with larger inbuilt DETECTARRAYS constant
cat <<EOS > $VERILATOR_CONFIG
\`verilator_config
lint_off -rule DETECTARRAY
EOS

