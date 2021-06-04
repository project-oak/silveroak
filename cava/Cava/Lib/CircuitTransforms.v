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

Require Import Cava.Core.Core.
Import Circuit.Notations.

Section WithCava.
  Context `{semantics : Cava}.

  (* identity circuit *)
  Definition Id {t} : Circuit t t := Comb Monad.ret.

  Definition Par {i1 i2 o1 o2} (c1 : Circuit i1 o1) (c2 : Circuit i2 o2)
    : Circuit (i1 * i2) (o1 * o2) :=
    First c1 >==> Second c2.
End WithCava.
