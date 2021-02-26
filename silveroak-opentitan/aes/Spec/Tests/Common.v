(****************************************************************************)
(* Copyright 2020 The Project Oak Authors                                   *)
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

Require Import Coq.Numbers.DecimalString.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import ExtLib.Data.Char.
Import ListNotations.
Local Open Scope string_scope.

Local Notation nat_to_string :=
  (fun n => NilZero.string_of_uint (Nat.to_uint n)) (only parsing).

(* Possible steps in the cipher *)
Inductive AESStep :=
| AddRoundKey
| MixColumns
| SubBytes
| ShiftRows
| InvMixColumns
| InvSubBytes
| InvShiftRows
.

Record TestVector {key state : Type} :=
  { plaintext : state;
    round_ksch : list key; (* part of the key schedule relevant to each round *)
    round_expected_states :
      list (list (AESStep * state)); (* for each round, list of intermediate
                                        states as (step * state after step) *)
  }.

Definition AESStep_to_string (step : AESStep) : string :=
  match step with
  | AddRoundKey => "AddRoundKey"
  | MixColumns => "MixColumns"
  | SubBytes => "SubBytes"
  | ShiftRows => "ShiftRows"
  | InvMixColumns => "InvMixColumns"
  | InvSubBytes => "InvSubBytes"
  | InvShiftRows => "InvShiftRows"
  end.

Record StepData {key state : Type} :=
  { step_round_index : nat;
    step_type : AESStep;
    step_key : key;
    state_before_step : state;
    state_after_step : state }.

(* input:  for each round, step * state post-step
   output: for each step, round idx * step * state pre-step * state post-step *)
Definition full_data_for_steps
           {key state : Type} (test : @TestVector key state)
  : list (@StepData key state) :=
  snd (List.fold_left
         (fun '(i,st,acc) '(exp,k) =>
            let exp' := snd (List.fold_left
                               (fun '(st,acc) '(step, st') =>
                                  let d := {| step_round_index := i;
                                              step_type := step;
                                              step_key := k;
                                              state_before_step := st;
                                              state_after_step := st' |} in
                                  (st', (acc ++ [d])%list))
                               exp (st,[])) in
            let st' := List.last (List.map snd exp) st in
            (S i, st', List.app acc exp'))
         (combine test.(round_expected_states) test.(round_ksch))
         (0%nat, test.(plaintext), [])).

(* TODO: create a string-based Utils file? *)
Definition newline := (String chr_newline "").

Section RunTest.
  Context {round_key state}
          (state_eqb : state -> state -> bool)
          (key_to_string : round_key -> string)
          (state_to_string : state -> string)
          (test : @TestVector round_key state)
          (impl : AESStep -> round_key -> state -> state).

  Inductive TestResult :=
  | Success : TestResult
  | Error : string -> TestResult
  .

  Definition format_error_message
             (data : @StepData round_key state) (result : state)
    : string :=
    ("Error in round " ++ nat_to_string data.(step_round_index) ++ ":")
      ++ (newline ++ "  after " ++ AESStep_to_string data.(step_type))
      ++ (" with (state=" ++ state_to_string data.(state_before_step) ++ ")")
      ++ (match data.(step_type) with
          | AddRoundKey =>
            newline ++ "                         (round key=" ++ key_to_string data.(step_key) ++ ")"
          | _ => "" (* don't print key for other steps; it's irrelevant *)
          end)
      ++ ","
      ++ (newline ++ "    expected " ++ state_to_string data.(state_after_step))
      ++ (newline ++ "    got      " ++ state_to_string result).

  Definition run_step (data : StepData) : TestResult :=
    let result := impl data.(step_type) data.(step_key) data.(state_before_step) in
    if state_eqb result data.(state_after_step)
    then Success
    else Error (format_error_message data result).

  Definition run_test : TestResult :=
    if (Nat.eqb (length (test.(round_expected_states))) (length (test.(round_ksch))))
    then
      let steps_data := full_data_for_steps test in
      let stepwise_results := List.map run_step steps_data in
      List.fold_left (fun out result =>
                        match out, result with
                        | _, Success => out
                        | Success, _ => result
                        | Error msg1, Error msg2 =>
                          Error (msg1 ++ newline ++ newline ++ msg2)
                        end) stepwise_results Success
    else Error ("Malformatted test; have keys for "
                  ++ (nat_to_string (length (test.(round_ksch))))
                  ++ " rounds but expected results for "
                  ++ (nat_to_string (length (test.(round_expected_states))))
                  ++ " rounds.").
End RunTest.

Definition pretty_print_step_data {key state}
           (key_to_string : key -> string)
           (state_to_string : state -> string)
           (data : @StepData key state) : string :=
  (("round " ++ nat_to_string data.(step_round_index))
     ++ (" " ++ AESStep_to_string data.(step_type))
     ++ (match data.(step_type) with
         | AddRoundKey => (" (key=" ++ key_to_string data.(step_key) ++ ")")
         | _ => ""
         end)
     ++ (newline ++ "    " ++ state_to_string data.(state_before_step))
     ++ " ==> " ++ state_to_string data.(state_after_step)).

Definition pretty_print_test_vector {key state}
           (key_to_string : key -> string)
           (state_to_string : state -> string)
           (test : @TestVector key state) : string :=
  String.concat
    newline
    (List.map (pretty_print_step_data key_to_string state_to_string)
              (full_data_for_steps test)).

(* Decidable equivalence test for AES steps *)
Definition AESStep_eqb (step1 step2 : AESStep) : bool :=
  match step1 with
  | AddRoundKey => match step2 with
                  | AddRoundKey => true
                  | _ => false
                  end
  | MixColumns => match step2 with
                  | MixColumns => true
                  | _ => false
                  end
  | SubBytes => match step2 with
                  | SubBytes => true
                  | _ => false
                  end
  | ShiftRows => match step2 with
                  | ShiftRows => true
                  | _ => false
                  end
  | InvMixColumns => match step2 with
                  | InvMixColumns => true
                  | _ => false
                  end
  | InvSubBytes => match step2 with
                  | InvSubBytes => true
                  | _ => false
                  end
  | InvShiftRows => match step2 with
                  | InvShiftRows => true
                  | _ => false
                   end
  end.

Definition get_state_inputs_for_round {state} (step : AESStep)
           (state_before_round : state)
           (round : list (AESStep * state))
  : list state :=
  (* Get the indices at which our desired step occurs *)
  let step_indices := filter (fun i => match nth_error round i with
                                    | None => false
                                    | Some x => AESStep_eqb step (fst x)
                                    end) (seq 0 (length round)) in
  (* because the state listed for each step is the state *after* the step, we
     need to find *previous* states to get the inputs to this AES step; shift
     the list by adding state_before_round to the front *)
  let default := state_before_round in (* for nth_default *)
  map (fun i => nth i (state_before_round :: map snd round) default)
      step_indices.
Definition get_state_outputs_for_round {state} (step : AESStep)
           (round : list (AESStep * state))
  : list state :=
  map snd (filter (fun x => AESStep_eqb step (fst x)) round).

(* Get all output states of a particular step from FIPS test vector *)
Definition get_state_outputs {key state} (step : AESStep) (test : @TestVector key state)
  : list state :=
  flat_map
    (get_state_outputs_for_round step)
    (test.(round_expected_states)).

(* Get all input states of a particular step from FIPS test vector *)
Definition get_state_inputs {key state} (step : AESStep) (test : @TestVector key state)
  : list state :=
  let default := test.(plaintext) in (* dummy value for last *)
  (* get the final state of each round *)
  let round_final_states :=
      map (fun round_states => last round_states default)
          (map (map snd) test.(round_expected_states)) in
  (* get the initial state of each round by shifting the final-states list 1
     place and adding the initial data *)
  let round_input_states := test.(plaintext) :: removelast round_final_states in
  flat_map
    (fun '(start_state, round) =>
       get_state_inputs_for_round step start_state round)
    (combine round_input_states test.(round_expected_states)).
