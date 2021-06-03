Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.ToCString.
Require Import coqutil.Word.Interface.
Require Import Bedrock2Experiments.Uart.Constants.
Require Import Bedrock2Experiments.LibBase.AbsMMIO.
Require Import Bedrock2Experiments.LibBase.Bitfield.

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

  (****
     static void uart_reset(void) {
       abs_mmio_write32(TOP_EARLGREY_UART0_BASE_ADDR + UART_CTRL_REG_OFFSET, 0u);

       // Write to the relevant bits clears the FIFOs.
       uint32_t reg = 0;
       reg = bitfield_bit32_write(reg, UART_FIFO_CTRL_RXRST_BIT, true);
       reg = bitfield_bit32_write(reg, UART_FIFO_CTRL_TXRST_BIT, true);
       abs_mmio_write32(TOP_EARLGREY_UART0_BASE_ADDR + UART_FIFO_CTRL_REG_OFFSET,
     reg);

       abs_mmio_write32(TOP_EARLGREY_UART0_BASE_ADDR + UART_OVRD_REG_OFFSET, 0u);
       abs_mmio_write32(TOP_EARLGREY_UART0_BASE_ADDR + UART_TIMEOUT_CTRL_REG_OFFSET,
     0u);
       abs_mmio_write32(TOP_EARLGREY_UART0_BASE_ADDR + UART_INTR_ENABLE_REG_OFFSET,
     0u);
       abs_mmio_write32(TOP_EARLGREY_UART0_BASE_ADDR + UART_INTR_STATE_REG_OFFSET,
     UINT32_MAX);
     }
   ***)
  Definition uart_reset : func :=
    let reg := "reg" in
    ("br2_uart_reset", ([], [],
    bedrock_func_body:(
      abs_mmio_write32(TOP_EARLGREY_UART0_BASE_ADDR + UART_CTRL_REG_OFFSET, 0);

      reg = 0;
      unpack! reg = bitfield_bit32_write(reg, UART_FIFO_CTRL_RXRST_BIT, 1);
      unpack! reg = bitfield_bit32_write(reg, UART_FIFO_CTRL_TXRST_BIT, 1);
      abs_mmio_write32(TOP_EARLGREY_UART0_BASE_ADDR + UART_FIFO_CTRL_REG_OFFSET, reg);

      abs_mmio_write32(TOP_EARLGREY_UART0_BASE_ADDR + UART_OVRD_REG_OFFSET, 0);
      abs_mmio_write32(TOP_EARLGREY_UART0_BASE_ADDR + UART_TIMEOUT_CTRL_REG_OFFSET, 0);
      abs_mmio_write32(TOP_EARLGREY_UART0_BASE_ADDR + UART_INTR_ENABLE_REG_OFFSET, 0);
      (* -1ULL instead of UINT32_MAX *)
      abs_mmio_write32(TOP_EARLGREY_UART0_BASE_ADDR + UART_INTR_STATE_REG_OFFSET, -1)
    ))).

  (****
     rom_error_t uart_init(uint32_t precalculated_nco) {
       if (precalculated_nco == 0 || precalculated_nco & ~UART_CTRL_NCO_MASK) {
         return kErrorUartInvalidArgument;
       }

       // Must be called before the first write to any of the UART registers.
       uart_reset();

       // Set baudrate, TX, no parity bits.
       uint32_t reg = 0;
       reg = bitfield_field32_write(reg, UART_CTRL_NCO_FIELD, precalculated_nco);
       reg = bitfield_bit32_write(reg, UART_CTRL_TX_BIT, true);
       reg = bitfield_bit32_write(reg, UART_CTRL_PARITY_EN_BIT, false);
       abs_mmio_write32(TOP_EARLGREY_UART0_BASE_ADDR + UART_CTRL_REG_OFFSET, reg);

       // Disable interrupts.
       abs_mmio_write32(TOP_EARLGREY_UART0_BASE_ADDR + UART_INTR_ENABLE_REG_OFFSET,
       0u);
       return kErrorOk;
     }
   ***)
  Definition uart_init : func :=
    let precalculated_nco := "precalculated_nco" in
    let reg := "reg" in
    let out := "out" in
    ("br2_uart_init", ([precalculated_nco], [out],
    bedrock_func_body:(
      if (precalculated_nco == 0) {
        out = kErrorUartInvalidArgument
      } else {
        if ((precalculated_nco & (UART_CTRL_NCO_MASK^(-1))) == 0) {
          uart_reset();

          reg = 0;
          unpack! reg = bitfield_field32_write(reg, UART_CTRL_NCO_FIELD, precalculated_nco);
          unpack! reg = bitfield_bit32_write(reg, UART_CTRL_TX_BIT, 1);
          unpack! reg = bitfield_bit32_write(reg, UART_CTRL_PARITY_EN_BIT, 0);
          abs_mmio_write32(TOP_EARLGREY_UART0_BASE_ADDR + UART_CTRL_REG_OFFSET, reg);
          abs_mmio_write32(TOP_EARLGREY_UART0_BASE_ADDR + UART_INTR_ENABLE_REG_OFFSET, 0);
          out = kErrorOk
        } else {
          out = kErrorUartInvalidArgument
        }
      }
    ))).

End Impl.
