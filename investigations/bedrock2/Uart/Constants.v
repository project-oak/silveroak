Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import coqutil.Word.Interface.
Require Import Bedrock2Experiments.Word.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

(* Core class : defines all the constants *)
Class uart_constants T :=
  {
    (* generated hw/top_earlgrey/sw/autogen/top_earlgrey.h *)
    TOP_EARLGREY_UART0_BASE_ADDR  : T;

    (* generated uart_regs.h *)
    UART_CTRL_NCO_MASK            : T;
    UART_CTRL_NCO_FIELD           : T;
    UART_CTRL_TX_BIT              : T;
    UART_CTRL_PARITY_EN_BIT       : T;
    UART_CTRL_REG_OFFSET          : T;
    UART_FIFO_CTRL_RXRST_BIT      : T;
    UART_FIFO_CTRL_TXRST_BIT      : T;
    UART_FIFO_CTRL_REG_OFFSET     : T;
    UART_OVRD_REG_OFFSET          : T;
    UART_TIMEOUT_CTRL_REG_OFFSET  : T;
    UART_INTR_ENABLE_REG_OFFSET   : T;
    UART_INTR_STATE_REG_OFFSET    : T;
    UART_STATUS_REG_OFFSET        : T;
    UART_STATUS_TXFULL_BIT        : T;
    UART_STATUS_TXIDLE_BIT        : T;
    UART_WDATA_WDATA_FIELD        : T;
    UART_WDATA_REG_OFFSET         : T;

    (* sw/device/silicon_creator/lib/drivers/uart.c *)
    NCO_WIDTH                    : T;

    (* sw/device/silicon_creator/lib/error.h *)
    kModuleUart                   : T; (* enum module_ *)
    kErrorOk                      : T; (* DEFINE_ERRORS *)
    kErrorUartInvalidArgument     : T; (* DEFINE_ERRORS *)
    kErrorUartBadBaudRate         : T; (* DEFINE_ERRORS *)
  }.

(* Given the string names of all constants, coerce them to bedroc2
   expressions with expr.var *)
Definition constant_vars
  {names : uart_constants string}
  : uart_constants expr :=
  {|
    (* generated hw/top_earlgrey/sw/autogen/top_earlgrey.h *)
    TOP_EARLGREY_UART0_BASE_ADDR := expr.var TOP_EARLGREY_UART0_BASE_ADDR;

    (* generated uart_regs.h *)
    UART_CTRL_NCO_MASK := expr.var UART_CTRL_NCO_MASK;
    UART_CTRL_NCO_FIELD := expr.var UART_CTRL_NCO_FIELD;
    UART_CTRL_TX_BIT := expr.var UART_CTRL_TX_BIT;
    UART_CTRL_PARITY_EN_BIT := expr.var UART_CTRL_PARITY_EN_BIT;
    UART_CTRL_REG_OFFSET := expr.var UART_CTRL_REG_OFFSET;
    UART_FIFO_CTRL_RXRST_BIT := expr.var UART_FIFO_CTRL_RXRST_BIT;
    UART_FIFO_CTRL_TXRST_BIT := expr.var UART_FIFO_CTRL_TXRST_BIT;
    UART_FIFO_CTRL_REG_OFFSET := expr.var UART_FIFO_CTRL_REG_OFFSET;
    UART_OVRD_REG_OFFSET := expr.var UART_OVRD_REG_OFFSET;
    UART_TIMEOUT_CTRL_REG_OFFSET := expr.var UART_TIMEOUT_CTRL_REG_OFFSET;
    UART_INTR_ENABLE_REG_OFFSET := expr.var UART_INTR_ENABLE_REG_OFFSET;
    UART_INTR_STATE_REG_OFFSET := expr.var UART_INTR_STATE_REG_OFFSET;
    UART_STATUS_REG_OFFSET := expr.var UART_STATUS_REG_OFFSET;
    UART_STATUS_TXFULL_BIT := expr.var UART_STATUS_TXFULL_BIT;
    UART_STATUS_TXIDLE_BIT := expr.var UART_STATUS_TXIDLE_BIT;
    UART_WDATA_WDATA_FIELD := expr.var UART_WDATA_WDATA_FIELD;
    UART_WDATA_REG_OFFSET := expr.var UART_WDATA_REG_OFFSET;

    (* sw/device/silicon_creator/lib/drivers/uart.c *)
    NCO_WIDTH := expr.var NCO_WIDTH;

    (* sw/device/silicon_creator/lib/error.h *)
    kModuleUart := expr.var kModuleUart;
    kErrorOk := expr.var kErrorOk;
    kErrorUartInvalidArgument := expr.var kErrorUartInvalidArgument;
    kErrorUartBadBaudRate := expr.var kErrorUartBadBaudRate;
  |}.

(* This instance provide the string name for each constant *)
Definition constant_names : uart_constants string :=
  {|
    (* generated hw/top_earlgrey/sw/autogen/top_earlgrey.h *)
    TOP_EARLGREY_UART0_BASE_ADDR := "TOP_EARLGREY_UART0_BASE_ADDR";

    (* generated uart_regs.h *)
    UART_CTRL_NCO_MASK := "UART_CTRL_NCO_MASK";
    UART_CTRL_NCO_FIELD := "UART_CTRL_NCO_FIELD";
    UART_CTRL_TX_BIT := "UART_CTRL_TX_BIT";
    UART_CTRL_PARITY_EN_BIT := "UART_CTRL_PARITY_EN_BIT";
    UART_CTRL_REG_OFFSET := "UART_CTRL_REG_OFFSET";
    UART_FIFO_CTRL_RXRST_BIT := "UART_FIFO_CTRL_RXRST_BIT";
    UART_FIFO_CTRL_TXRST_BIT := "UART_FIFO_CTRL_TXRST_BIT";
    UART_FIFO_CTRL_REG_OFFSET := "UART_FIFO_CTRL_REG_OFFSET";
    UART_OVRD_REG_OFFSET := "UART_OVRD_REG_OFFSET";
    UART_TIMEOUT_CTRL_REG_OFFSET := "UART_TIMEOUT_CTRL_REG_OFFSET";
    UART_INTR_ENABLE_REG_OFFSET := "UART_INTR_ENABLE_REG_OFFSET";
    UART_INTR_STATE_REG_OFFSET := "UART_INTR_STATE_REG_OFFSET";
    UART_STATUS_REG_OFFSET := "UART_STATUS_REG_OFFSET";
    UART_STATUS_TXFULL_BIT := "UART_STATUS_TXFULL_BIT";
    UART_STATUS_TXIDLE_BIT := "UART_STATUS_TXIDLE_BIT";
    UART_WDATA_WDATA_FIELD := "UART_WDATA_WDATA_FIELD";
    UART_WDATA_REG_OFFSET := "UART_WDATA_REG_OFFSET";

    (* sw/device/silicon_creator/lib/drivers/uart.c *)
    NCO_WIDTH := "NCO_WIDTH";

    (* sw/device/silicon_creator/lib/error.h *)
    kModuleUart := "kModuleUart";
    kErrorOk := "kErrorOk";
    kErrorUartInvalidArgument := "kErrorUartInvalidArgument";
    kErrorUartBadBaudRate := "kErrorUartBadBaudRate";
  |}.
