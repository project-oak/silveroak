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
  Local Notation "-1" := (expr.literal 4294967295) (in custom bedrock_expr).

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
    let temp := "temp" in
    ("b2_uart_reset", ([TOP_EARLGREY_UART0_BASE_ADDR; UART_CTRL_REG_OFFSET;
    UART_FIFO_CTRL_RXRST_BIT;UART_FIFO_CTRL_TXRST_BIT;UART_FIFO_CTRL_REG_OFFSET;
    UART_OVRD_REG_OFFSET;UART_TIMEOUT_CTRL_REG_OFFSET;UART_INTR_ENABLE_REG_OFFSET;
    UART_INTR_STATE_REG_OFFSET], [],
    bedrock_func_body:(
      temp = TOP_EARLGREY_UART0_BASE_ADDR + UART_CTRL_REG_OFFSET;
      abs_mmio_write32(temp, 0);

      reg = 0;
      temp = UART_FIFO_CTRL_RXRST_BIT;
      unpack! reg = bitfield_bit32_write(reg, temp, 1);
      temp = UART_FIFO_CTRL_TXRST_BIT;
      unpack! reg = bitfield_bit32_write(reg, temp, 1);
      temp = TOP_EARLGREY_UART0_BASE_ADDR + UART_FIFO_CTRL_REG_OFFSET;
      abs_mmio_write32(temp, reg);

      temp = TOP_EARLGREY_UART0_BASE_ADDR + UART_OVRD_REG_OFFSET;
      abs_mmio_write32(temp, 0);
      temp = TOP_EARLGREY_UART0_BASE_ADDR + UART_TIMEOUT_CTRL_REG_OFFSET;
      abs_mmio_write32(temp, 0);
      temp = TOP_EARLGREY_UART0_BASE_ADDR + UART_INTR_ENABLE_REG_OFFSET;
      abs_mmio_write32(temp, 0);
      (* -1 instead of UINT32_MAX *)
      temp = TOP_EARLGREY_UART0_BASE_ADDR + UART_INTR_STATE_REG_OFFSET;
      abs_mmio_write32(temp, -1)
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
    let temp1 := "temp1" in
    let temp2 := "temp2" in
    let out := "out" in
    ("b2_uart_init", ([UART_CTRL_NCO_MASK; UART_CTRL_NCO_OFFSET; UART_CTRL_TX_BIT;
    UART_CTRL_PARITY_EN_BIT; UART_CTRL_REG_OFFSET; UART_INTR_ENABLE_REG_OFFSET;
    kErrorOk; kErrorUartInvalidArgument; TOP_EARLGREY_UART0_BASE_ADDR;
    UART_FIFO_CTRL_RXRST_BIT; UART_FIFO_CTRL_TXRST_BIT; UART_FIFO_CTRL_REG_OFFSET;
    UART_OVRD_REG_OFFSET; UART_TIMEOUT_CTRL_REG_OFFSET; UART_INTR_STATE_REG_OFFSET;
    precalculated_nco], [out],
    bedrock_func_body:(
      if (precalculated_nco == 0) {
        out = kErrorUartInvalidArgument
      } else {
        if ((precalculated_nco & (UART_CTRL_NCO_MASK^(-1))) == 0) {
          uart_reset(TOP_EARLGREY_UART0_BASE_ADDR, UART_CTRL_REG_OFFSET,
            UART_FIFO_CTRL_RXRST_BIT, UART_FIFO_CTRL_TXRST_BIT, UART_FIFO_CTRL_REG_OFFSET,
            UART_OVRD_REG_OFFSET, UART_TIMEOUT_CTRL_REG_OFFSET, UART_INTR_ENABLE_REG_OFFSET,
            UART_INTR_STATE_REG_OFFSET);

          reg = 0;
          temp1 = UART_CTRL_NCO_MASK;
          temp2 = UART_CTRL_NCO_OFFSET;
          unpack! reg = bitfield_field32_write(reg, temp1, temp2, precalculated_nco);
          temp1 = UART_CTRL_TX_BIT;
          unpack! reg = bitfield_bit32_write(reg, temp1, 1);
          temp1 = UART_CTRL_PARITY_EN_BIT;
          unpack! reg = bitfield_bit32_write(reg, temp1, 0);
          temp1 = TOP_EARLGREY_UART0_BASE_ADDR + UART_CTRL_REG_OFFSET;
          abs_mmio_write32(temp1, reg);
          temp1 = TOP_EARLGREY_UART0_BASE_ADDR + UART_INTR_ENABLE_REG_OFFSET;
          abs_mmio_write32(temp1, 0);
          out = kErrorOk
        } else {
          out = kErrorUartInvalidArgument
        }
      }
    ))).

  (****
    static bool uart_tx_full(void) {
      uint32_t reg =
          abs_mmio_read32(TOP_EARLGREY_UART0_BASE_ADDR + UART_STATUS_REG_OFFSET);
      return bitfield_bit32_read(reg, UART_STATUS_TXFULL_BIT);
    }
   ***)
  Definition uart_tx_full : func :=
    let reg := "reg" in
    let temp := "temp" in
    let out := "out" in
    ("b2_uart_tx_full", ([TOP_EARLGREY_UART0_BASE_ADDR; UART_STATUS_REG_OFFSET;
    UART_STATUS_TXFULL_BIT], [out],
    bedrock_func_body:(
      temp = TOP_EARLGREY_UART0_BASE_ADDR + UART_STATUS_REG_OFFSET;
      unpack! reg = abs_mmio_read32(temp);
      temp = UART_STATUS_TXFULL_BIT;
      unpack! out = bitfield_bit32_read(reg, temp)
    ))).

  (****
    static bool uart_tx_idle(void) {
      uint32_t reg =
          abs_mmio_read32(TOP_EARLGREY_UART0_BASE_ADDR + UART_STATUS_REG_OFFSET);
      return bitfield_bit32_read(reg, UART_STATUS_TXIDLE_BIT);
    }
   ***)
  Definition uart_tx_idle : func :=
    let reg := "reg" in
    let temp := "temp" in
    let out := "out" in
    ("b2_uart_tx_idle", ([TOP_EARLGREY_UART0_BASE_ADDR; UART_STATUS_REG_OFFSET;
    UART_STATUS_TXIDLE_BIT], [out],
    bedrock_func_body:(
      temp = TOP_EARLGREY_UART0_BASE_ADDR + UART_STATUS_REG_OFFSET;
      unpack! reg = abs_mmio_read32(temp);
      temp = UART_STATUS_TXIDLE_BIT;
      unpack! out = bitfield_bit32_read(reg, temp)
    ))).

  (****
    void uart_putchar(uint8_t byte) {
      // If the transmit FIFO is full, wait.
      while (uart_tx_full()) {
      }
      uint32_t reg = bitfield_field32_write(0, UART_WDATA_WDATA_FIELD, byte);
      abs_mmio_write32(TOP_EARLGREY_UART0_BASE_ADDR + UART_WDATA_REG_OFFSET, reg);

      // If the transmitter is active, wait.
      while (!uart_tx_idle()) {
      }
    }
   ***)
  Definition uart_putchar : func :=
    let byte := "byte" in
    let reg := "reg" in
    let temp1 := "temp1" in
    let temp2 := "temp2" in
    let cond := "cond" in
    ("b2_uart_putchar", ([UART_WDATA_WDATA_MASK; UART_WDATA_WDATA_OFFSET;
    TOP_EARLGREY_UART0_BASE_ADDR; UART_WDATA_REG_OFFSET; UART_STATUS_REG_OFFSET;
    UART_STATUS_TXIDLE_BIT; UART_STATUS_TXFULL_BIT; byte], [],
    bedrock_func_body:(
      unpack! cond = uart_tx_full(TOP_EARLGREY_UART0_BASE_ADDR, UART_STATUS_REG_OFFSET,
                                  UART_STATUS_TXFULL_BIT);
      while (cond == 1) {
        unpack! cond = uart_tx_full(TOP_EARLGREY_UART0_BASE_ADDR, UART_STATUS_REG_OFFSET,
                                    UART_STATUS_TXFULL_BIT)
      };
      temp1 = UART_WDATA_WDATA_MASK;
      temp2 = UART_WDATA_WDATA_OFFSET;
      unpack! reg = bitfield_field32_write(0, temp1, temp2, byte);
      temp1 = TOP_EARLGREY_UART0_BASE_ADDR + UART_WDATA_REG_OFFSET;
      abs_mmio_write32(temp1, reg);
      unpack! cond = uart_tx_idle(TOP_EARLGREY_UART0_BASE_ADDR, UART_STATUS_REG_OFFSET,
                                  UART_STATUS_TXIDLE_BIT);
      while (cond == 0) {
        unpack! cond = uart_tx_idle(TOP_EARLGREY_UART0_BASE_ADDR, UART_STATUS_REG_OFFSET,
                                    UART_STATUS_TXIDLE_BIT)
      }
    ))).

  (****
    size_t uart_write(const uint8_t *data, size_t len) {
      size_t total = len;
      while (len) {
        uart_putchar( *data);
        data++;
        len--;
      }
      return total;
    }
   ***)
  Definition uart_write : func :=
    let data := "data" in
    let len := "len" in
    let total := "total" in
    let out := "out" in
    ("b2_uart_write", ([UART_WDATA_WDATA_MASK; UART_WDATA_WDATA_OFFSET;
                        TOP_EARLGREY_UART0_BASE_ADDR; UART_WDATA_REG_OFFSET; UART_STATUS_REG_OFFSET;
                        UART_STATUS_TXIDLE_BIT; UART_STATUS_TXFULL_BIT;
                        data; len], [out],
    bedrock_func_body:(
      total = len;
      while (0 < len) {
        uart_putchar(UART_WDATA_WDATA_MASK, UART_WDATA_WDATA_OFFSET,
                     TOP_EARLGREY_UART0_BASE_ADDR, UART_WDATA_REG_OFFSET,
                     UART_STATUS_REG_OFFSET, UART_STATUS_TXIDLE_BIT, UART_STATUS_TXFULL_BIT,
                     load4(data));
        data = data + 1;
        len = len - 1
      };
      out = total
    ))).

  (***
    size_t uart_sink(void *uart, const char *data, size_t len) {
      (void)uart;
      return uart_write((const uint8_t * )data, len);
    }
   ***)
  Definition uart_sink : func :=
    let uart := "uart" in
    let data := "data" in
    let len := "len" in
    let out := "out" in
    ("b2_uart_sink", ([UART_WDATA_WDATA_MASK; UART_WDATA_WDATA_OFFSET;
                       TOP_EARLGREY_UART0_BASE_ADDR; UART_WDATA_REG_OFFSET;
                       uart; data; len], [out],
    bedrock_func_body:(
      unpack! out = uart_write(UART_WDATA_WDATA_MASK, UART_WDATA_WDATA_OFFSET,
                               TOP_EARLGREY_UART0_BASE_ADDR, UART_WDATA_REG_OFFSET,
                               data, len)
    ))).

End Impl.
