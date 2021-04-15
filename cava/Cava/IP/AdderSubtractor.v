(****************************************************************************)
(* Copyright 2021 The Project Oak Authors                                   *)
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

Require Import Cava.Cava.

Section WithCava.
  Context `{semantics:Cava}.

  Definition c_addsub_0 (input : signal (Vec Bit 8) * signal (Vec Bit 8))
    : cava (signal (Vec Bit 9))
    := let '(x,y) := input in
       '(sum, carry) <- addC (x,y,zero) ;;
       Vec.shiftin carry sum.

End WithCava.
