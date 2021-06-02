Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.ToCString.
Require Import coqutil.Word.Interface.
Require Import Bedrock2Experiments.Uart.Constants.
Require Import Bedrock2Experiments.Uart.Mmio.
Require Import Bedrock2Experiments.Uart.Bitfield.

Import Syntax.Coercions List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section Impl.
  Local Existing Instance constant_names.
  Local Existing Instance constant_vars.

  (* Notations for small constants *)
  Local Notation "0" := (expr.literal 0) (in custom bedrock_expr).
  Local Notation "1" := (expr.literal 1) (in custom bedrock_expr).
  Local Notation "-1" := (expr.literal (- 1)) (in custom bedrock_expr).

  (* sw/device/silicon_creator/lib/drivers/uart.c *)

  (* static void uart_reset(const uart_t *uart) *)
  Definition uart_reset : func :=
    let uart := "uart" in
    let uart_base_addr := "uart_base_addr" in
    let reg := "reg" in
    ("br2_uart_reset", ([], [],
    bedrock_func_body:(
      (* uart->base_addr *)
      uart_base_addr = load4(uart);
      mmio_region_write32(uart_base_addr, UART_CTRL_REG_OFFSET, 0);

      reg = 0;
      unpack! reg = bitfield_bit32_write(reg, UART_FIFO_CTRL_RXRST_BIT, 1);
      unpack! reg = bitfield_bit32_write(reg, UART_FIFO_CTRL_TXRST_BIT, 1);
      mmio_region_write32(uart_base_addr, UART_FIFO_CTRL_REG_OFFSET, reg);

      mmio_region_write32(uart_base_addr, UART_OVRD_REG_OFFSET, 0);
      mmio_region_write32(uart_base_addr, UART_TIMEOUT_CTRL_REG_OFFSET, 0);
      mmio_region_write32(uart_base_addr, UART_INTR_ENABLE_REG_OFFSET, 0);
      (* -1ULL instead of UINT32_MAX *)
      mmio_region_write32(uart_base_addr, UART_INTR_STATE_REG_OFFSET, -1)
    ))).

End Impl.
