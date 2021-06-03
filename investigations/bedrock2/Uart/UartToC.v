Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax.
Require Import bedrock2.ToCString.
Require Import bedrock2.Variables.
Require Import coqutil.Z.HexNotation.
Require Import Bedrock2Experiments.Uart.Uart.
Require Import Bedrock2Experiments.LibBase.Bitfield.
Require Import Bedrock2Experiments.LibBase.AbsMMIO.
Require Import Bedrock2Experiments.Uart.Constants.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Existing Instance constant_names.

Definition funcs := [
  bitfield_field32_write
  ;bitfield_field32_read
  ;bitfield_bit32_read
  ;bitfield_bit32_write
  ;abs_mmio_write32
  ;abs_mmio_read32
  ;uart_reset
  ].

Definition make_uart_c :=
  concat LF (map (fun f => "static " ++ c_func f) funcs).

Redirect "uart.c" Compute make_uart_c.
