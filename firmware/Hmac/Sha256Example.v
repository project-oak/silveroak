Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.
Require Import coqutil.Word.Interface.
Require Import Bedrock2Experiments.Hmac.Hmac.
Import Syntax.Coercions List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition b2_sha256: func :=
  let digest := "digest" in
  let msg := "msg" in
  let msg_len := "msg_len" in
  let ignored_result := "ignored_result" in
  ("b2_sha256",
   ([digest; msg; msg_len], [], bedrock_func_body:(
     b2_hmac_sha256_init();
     unpack! ignored_result = b2_hmac_sha256_update(msg, msg_len);
     unpack! ignored_result = b2_hmac_sha256_final(digest)
  ))).
