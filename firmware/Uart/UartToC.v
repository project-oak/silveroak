Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax.
Require Import bedrock2.ToCString.
Require Import bedrock2.Variables.
Require Import coqutil.Z.HexNotation.
Require Import Bedrock2Experiments.Uart.Uart.
Require Import Bedrock2Experiments.LibBase.Bitfield.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition uart_c_template_top : string :=
  "// Autogenerated from Coq based on LowRISC implementation

// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include ""sw/device/silicon_creator/lib/drivers/uart.h""

#include ""sw/device/lib/base/memory.h"" // for bedrock2


#include ""sw/device/lib/arch/device.h""
#include ""sw/device/lib/base/bitfield.h""
#include ""sw/device/silicon_creator/lib/base/abs_mmio.h""
#include ""sw/device/silicon_creator/lib/error.h""

#include ""hw/top_earlgrey/sw/autogen/top_earlgrey.h""
#include ""uart_regs.h""  // Generated.

static inline uintptr_t _br2_load(uintptr_t a, size_t sz) {
  uintptr_t r = 0;
  memcpy(&r, (void*)a, sz);
  return r;
}".

Definition uart_c_template_bottom : string :=
  "rom_error_t uart_init(uint32_t precalculated_nco) {
  return b2_uart_init((uintptr_t) precalculated_nco);
}

void uart_putchar(uint8_t byte) {
  b2_uart_putchar((uintptr_t) byte);
}

size_t uart_write(const uint8_t *data, size_t len) {
  return b2_uart_write((uintptr_t) data, (uintptr_t) len);
}

size_t uart_sink(void *uart, const char *data, size_t len) {
  return b2_uart_sink((uintptr_t) uart, (uintptr_t) data, (uintptr_t) len);
}".

Definition funcs := [
  bitfield_field32_write
  ;bitfield_field32_read
  ;bitfield_bit32_read
  ;bitfield_bit32_write
  ;uart_reset
  ;uart_init
  ;uart_tx_full
  ;uart_tx_idle
  ;uart_putchar
  ;uart_write
  ;uart_sink
  ].

Definition make_uart_c :=
  uart_c_template_top ++
  concat LF (map (fun f => "static " ++ c_func f) funcs) ++
  uart_c_template_bottom.

Require Import bedrock2.Bytedump.
Local Open Scope bytedump_scope.
Goal True.
  (* Note: run using make/coqc to avoid IDE bugs causing missing newlines or spurious <infomsg>*)
  Redirect "uart.c"
    let c_code := eval compute in (byte_list_of_string make_uart_c) in idtac c_code.
Abort.
