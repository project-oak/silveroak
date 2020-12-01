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

TOPLEVEL=$(git rev-parse --show-toplevel)

# Use python2 because absolutize-imports.py is not executable
ABSOLUTIZE="python2 $TOPLEVEL/third_party/coq-tools/absolutize-imports.py --in-place -v"

COQPROJECTS=$(git ls-files --full-name $TOPLEVEL/*/ | grep _CoqProject | grep -v "^investigations/" | grep -v "^third_party")


# absolutize-imports script pulls absolute names from .glob files, so we need to fully build first
echo "Building Coq files before absolutizing..."
make -j4 coq

for f in $COQPROJECTS;
do
	cd "$TOPLEVEL/$(dirname $f)";
	
	LIBS=$(grep "^\s*-[RIQ]" _CoqProject | xargs echo) # get library arguments from _CoqProject
	FILES=$(grep "\.v$" _CoqProject | xargs echo) # get .v files from _CoqProject

	echo "Absolutizing imports in $PWD...";
	echo "$ABSOLUTIZE $LIBS $FILES"; # print command being executed (helpful for debugging)
	$ABSOLUTIZE $LIBS $FILES;
done;
