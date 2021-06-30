Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.
Require Import coqutil.Word.Interface.
Require Import Bedrock2Experiments.Aes.Aes.
Require Import Bedrock2Experiments.Aes.Constants.
Import Syntax.Coercions List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(**** Usage example for AES firmware functions + proof; checks that proofs
      compose properly ****)

Section Impl.
  (* instantiated to `expr.literal SOME_Z_CONST` for proving and
     compilation using the bedrock2 compiler, instantiated to
     `expr.var STRING_NAME_OF_CONST` for pretty-printing to C code *)
  Context {constant_vars : aes_constants expr}.

  (* Notations for small constants *)
  Local Notation "0" := (expr.literal 0) (in custom bedrock_expr).

  Definition aes_encrypt : func :=
    let plaintext := "plaintext" in
    let key := "key" in
    let iv := "iv" in
    let ciphertext := "ciphertext" in
    ("b2_aes_encrypt",
     ([plaintext; key; iv; ciphertext], [], bedrock_func_body:(
       (* initialize the AES block :
          operation = kAesEnc, mode = kAesEcb, key_len = kAes256,
          manual_operation = 0 *)
       aes_init (kAesEnc, kAesEcb, kAes256, 0) ;

       (* write key and initialization vector *)
       aes_key_put (key, kAes256) ;
       aes_iv_put (iv) ;

       (* write input data *)
       aes_data_put_wait (plaintext) ;

       (* wait for output, write it to ciphertext *)
       aes_data_get_wait (ciphertext)
    ))).
End Impl.
