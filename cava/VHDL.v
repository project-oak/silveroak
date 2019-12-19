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

Require Import Program.Basics.
From Coq Require Import Bool.Bool.
From Coq Require Import Ascii String.
From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Import ListNotations.

Require Import Cava.

Local Open Scope list_scope.

Definition a : list string := [append ("alpha") ("beta")].

Definition entity (name : string) (netlist : CavaState) : list string :=
  match netlist with
  | mkCavaState o insts inputs outputs =>
      [append "entity " (append name " is ");
       append "end entity " (append name ";")]
  end.

(* But why can't I say this?

Definition entity2 (name : string) (netlist : CavaState) : list string :=
  match netlist with
  | mkCavaState o insts inputs outputs =>
      ["entity "%string ++ name " is "%string;
       "end entity "%string ++ name ++ ";"%string]
  end.

*)