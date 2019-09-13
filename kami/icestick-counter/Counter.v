(****************************************************************************)
(* Copyright 2019 The Project Oak Authors                                   *)
(*                                                                          *)
(* Licensed under the Apache License, Version 2.0 (the "License")           *)
(* you may not use this file except in compliance with the License.         *)
(* You may obtain a copy of the License at                                  *)
(*                                                                          *)
(*     http://www.apache.org/licenses/LICENSE-2.0                           *)
(*                                                                          *)
(* Unless required by applicable law or agreed to in writing, software      *)
(* distributed under the License is distributed on an "AS IS" BASIS,        *)
(* WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. *)
(* See the License for the specific language governing permissions and      *)
(* limitations under the License.                                           *)
(****************************************************************************)

Require Import Kami.
Require Import Kami.Syntax.
Require Import Kami.Synthesize.
Require Import Ext.BSyntax.
Require Import ExtrOcamlNatInt ExtrOcamlString.

Definition count := MethodSig ("counter" -- "count_value") (Bit 4) : Void.

Definition counter4 := MODULE {
    Register "counterReg" : Bit 4 <- $0

    with Rule "incrementAndOutput" :=
       Read val <- "counterReg";
       Write "counterReg" <- #val + ($1 :: Bit 4);
       (* Call count (#val); *)
       Retv

    with Method "count_value" () : (Bit 4) :=
       Read counterValue <- "counterReg";
       Ret #counterValue

  }.

Hint Unfold count : MethDefs.
Hint Unfold counter4 : ModuleDefs.

Extraction Language Ocaml.

Set Extraction Optimize.
Set Extraction KeepSingleton.
Unset Extraction AutoInline.

Definition targetCounter4 := ModulesSToBModules (getModuleS counter4).

Extraction "Counter.ml" targetCounter4.
