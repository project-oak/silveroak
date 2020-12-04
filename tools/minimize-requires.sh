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

# Do not use --absolutize here, because of https://github.com/JasonGross/coq-tools/issues/55
MINIMIZE="$TOPLEVEL/third_party/coq-tools/minimize-requires.py --in-place"

MAKECOQ="make -j4 coq"

COQPROJECTS=$(git ls-files --full-name $TOPLEVEL/*/ | grep _CoqProject | grep -v "^investigations/" | grep -v "^third_party")

# do not continue loop if failures are encountered
set -e

# minimize-requires script analyzes .glob files, so we need to fully build first
echo "Building all Coq files before minimizing..."
$MAKECOQ

for f in $COQPROJECTS;
do
	cd "$TOPLEVEL/$(dirname $f)";

	# re-make in case we have gotten out of sync with another directory
	$MAKECOQ

	LIBS=$(grep "^\s*-[RIQ]" _CoqProject | xargs echo) # get all library arguments from _CoqProject

	FILES=$(grep "\.v$" _CoqProject | xargs echo) # get .v files from _CoqProject

	# get library arguments that do NOT reference parent directories
	# (otherwise coqdep will include non-local files in the sorted list)
	LOCALLIBS=$(grep "^\s*-[RIQ]" _CoqProject | grep -v "^\s*-[RIQ]\s\+\.\." | xargs echo)
	FILES=$(coqdep -sort $LOCALLIBS $FILES) # sort using coqdep

	echo "Minimizing imports in $PWD...";
	echo "$MINIMIZE $LIBS $FILES"; # print command being executed (helpful for debugging)
	$MINIMIZE $LIBS $FILES;

	# re-make with fewer imports
	echo "Re-building Coq files in $PWD...";
	$MAKECOQ;
done;
