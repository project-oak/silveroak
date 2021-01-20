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

.PHONY: all clean coq haskell minimize-requires _CoqProject

all:		coq haskell

coq:		Makefile.coq
		$(MAKE) -f Makefile.coq

minimize-requires: coq
	../tools/minimize-requires.sh
	$(MAKE) coq

%.vo:		Makefile.coq
		$(MAKE) -f Makefile.coq $@

FixupHaskell:	FixupHaskell.hs
		ghc --make $^

haskell:	coq FixupHaskell
		./FixupHaskell
		mv Ascii2.hs Ascii.hs
		mv ByteVector2.hs ByteVector.hs
		runhaskell Setup.hs configure --user
		runhaskell Setup.hs build
		runhaskell Setup.hs install

Makefile.coq:	_CoqProject
		coq_makefile -f _CoqProject -o Makefile.coq

_CoqProject:
		@echo "INSTALLDEFAULTROOT = Cava" > _CoqProject
		@echo "-R Cava Cava" >> _CoqProject
		@echo "-R ../third_party/coq-ext-lib/theories ExtLib" >> _CoqProject
		@echo "-R ../third_party/bedrock2/deps/coqutil/src/coqutil coqutil" >> _CoqProject
		git ls-files | grep "\.v$$" >> _CoqProject

clean:
		-@$(MAKE) -f Makefile.coq clean
		rm -rf _CoqProject Makefile.coq Makefile.coq.conf dist
		git clean -Xfd
