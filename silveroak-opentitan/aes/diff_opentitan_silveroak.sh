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

set -eu

echo "** Please make sure third_party/opentitan does not contain modified RTL files"

rm -rf opentitan_gold
rm -rf opentitan_silveroak

cp -r ../../third_party/opentitan opentitan_gold
cp -r ../../third_party/opentitan opentitan_silveroak
./copy_silveroak_files.sh ./opentitan_silveroak

echo "** Sanity check: diff should report changes to files replaced by silveroak below:"
diff -qr opentitan_gold/ opentitan_silveroak/ || true
