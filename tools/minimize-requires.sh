#!/bin/bash
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

# do not continue if failures are encountered
set -e

TOPLEVEL=$(git rev-parse --show-toplevel)

# Do not use --absolutize here, because of https://github.com/JasonGross/coq-tools/issues/55
MINIMIZE="$TOPLEVEL/third_party/coq-tools/minimize-requires.py --in-place --all -f _CoqProject"


# TODO: remove if unneeded
# LIBS=$(grep "^\s*-[RIQ]" _CoqProject | xargs echo) # get all library arguments from _CoqProject
# FILES=$(grep "\.v$" _CoqProject | xargs echo) # get .v files from _CoqProject

echo "Minimizing imports in $PWD..."
echo "$MINIMIZE" # print command being executed (helpful for debugging)
$MINIMIZE
