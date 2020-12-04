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

# This script is a very simple wrapper that calls minimize-requires from coq-tools

# do not continue if failures are encountered
set -e

TOPLEVEL=$(git rev-parse --show-toplevel)

# Do not use --absolutize here, because of https://github.com/JasonGross/coq-tools/issues/55
MINIMIZE="$TOPLEVEL/third_party/coq-tools/minimize-requires.py --in-place --all -f _CoqProject"

echo "Minimizing imports in $PWD..."
echo "$MINIMIZE" # print command being executed (helpful for debugging)
$MINIMIZE
