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
    UART_CTRL_NCO_OFFSET          : T;
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
    UART_WDATA_WDATA_MASK         : T;
    UART_WDATA_WDATA_OFFSET       : T;
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
    UART_CTRL_NCO_OFFSET := expr.var UART_CTRL_NCO_OFFSET;
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
    UART_WDATA_WDATA_MASK := expr.var UART_WDATA_WDATA_MASK;
    UART_WDATA_WDATA_OFFSET := expr.var UART_WDATA_WDATA_OFFSET;
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
    UART_CTRL_NCO_OFFSET := "UART_CTRL_NCO_OFFSET";
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
    UART_WDATA_WDATA_MASK := "UART_WDATA_WDATA_MASK";
    UART_WDATA_WDATA_OFFSET := "UART_WDATA_WDATA_OFFSET";
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

(* Given the Z values of all the constants, coerce them to bedrock2
   expressions with expr.literal *)
Definition constant_literals
           {vals : uart_constants Z}
  : uart_constants expr :=
  {|
    (* generated hw/top_earlgrey/sw/autogen/top_earlgrey.h *)
    TOP_EARLGREY_UART0_BASE_ADDR := expr.literal TOP_EARLGREY_UART0_BASE_ADDR;

    (* generated uart_regs.h *)
    UART_CTRL_NCO_MASK := expr.literal UART_CTRL_NCO_MASK;
    UART_CTRL_NCO_OFFSET := expr.literal UART_CTRL_NCO_OFFSET;
    UART_CTRL_NCO_FIELD := expr.literal UART_CTRL_NCO_FIELD;
    UART_CTRL_TX_BIT := expr.literal UART_CTRL_TX_BIT;
    UART_CTRL_PARITY_EN_BIT := expr.literal UART_CTRL_PARITY_EN_BIT;
    UART_CTRL_REG_OFFSET := expr.literal UART_CTRL_REG_OFFSET;
    UART_FIFO_CTRL_RXRST_BIT := expr.literal UART_FIFO_CTRL_RXRST_BIT;
    UART_FIFO_CTRL_TXRST_BIT := expr.literal UART_FIFO_CTRL_TXRST_BIT;
    UART_FIFO_CTRL_REG_OFFSET := expr.literal UART_FIFO_CTRL_REG_OFFSET;
    UART_OVRD_REG_OFFSET := expr.literal UART_OVRD_REG_OFFSET;
    UART_TIMEOUT_CTRL_REG_OFFSET := expr.literal UART_TIMEOUT_CTRL_REG_OFFSET;
    UART_INTR_ENABLE_REG_OFFSET := expr.literal UART_INTR_ENABLE_REG_OFFSET;
    UART_INTR_STATE_REG_OFFSET := expr.literal UART_INTR_STATE_REG_OFFSET;
    UART_STATUS_REG_OFFSET := expr.literal UART_STATUS_REG_OFFSET;
    UART_STATUS_TXFULL_BIT := expr.literal UART_STATUS_TXFULL_BIT;
    UART_STATUS_TXIDLE_BIT := expr.literal UART_STATUS_TXIDLE_BIT;
    UART_WDATA_WDATA_MASK := expr.literal UART_WDATA_WDATA_MASK;
    UART_WDATA_WDATA_OFFSET := expr.literal UART_WDATA_WDATA_OFFSET;
    UART_WDATA_WDATA_FIELD := expr.literal UART_WDATA_WDATA_FIELD;
    UART_WDATA_REG_OFFSET := expr.literal UART_WDATA_REG_OFFSET;

    (* sw/device/silicon_creator/lib/drivers/uart.c *)
    NCO_WIDTH := expr.literal NCO_WIDTH;

    (* sw/device/silicon_creator/lib/error.h *)
    kModuleUart := expr.literal kModuleUart;
    kErrorOk := expr.literal kErrorOk;
    kErrorUartInvalidArgument := expr.literal kErrorUartInvalidArgument;
    kErrorUartBadBaudRate := expr.literal kErrorUartBadBaudRate;
  |}.

(* Given the Z values of all the constants, convert them to words with
   word.of_Z *)
Definition constant_words
           {width} {word : word width} {word_ok : word.ok word}
           {vals : uart_constants Z}
  : uart_constants word :=
  {|
    (* generated hw/top_earlgrey/sw/autogen/top_earlgrey.h *)
    TOP_EARLGREY_UART0_BASE_ADDR := word.of_Z TOP_EARLGREY_UART0_BASE_ADDR;

    (* generated uart_regs.h *)
    UART_CTRL_NCO_MASK := word.of_Z UART_CTRL_NCO_MASK;
    UART_CTRL_NCO_OFFSET := word.of_Z UART_CTRL_NCO_OFFSET;
    UART_CTRL_NCO_FIELD := word.of_Z UART_CTRL_NCO_FIELD;
    UART_CTRL_TX_BIT := word.of_Z UART_CTRL_TX_BIT;
    UART_CTRL_PARITY_EN_BIT := word.of_Z UART_CTRL_PARITY_EN_BIT;
    UART_CTRL_REG_OFFSET := word.of_Z UART_CTRL_REG_OFFSET;
    UART_FIFO_CTRL_RXRST_BIT := word.of_Z UART_FIFO_CTRL_RXRST_BIT;
    UART_FIFO_CTRL_TXRST_BIT := word.of_Z UART_FIFO_CTRL_TXRST_BIT;
    UART_FIFO_CTRL_REG_OFFSET := word.of_Z UART_FIFO_CTRL_REG_OFFSET;
    UART_OVRD_REG_OFFSET := word.of_Z UART_OVRD_REG_OFFSET;
    UART_TIMEOUT_CTRL_REG_OFFSET := word.of_Z UART_TIMEOUT_CTRL_REG_OFFSET;
    UART_INTR_ENABLE_REG_OFFSET := word.of_Z UART_INTR_ENABLE_REG_OFFSET;
    UART_INTR_STATE_REG_OFFSET := word.of_Z UART_INTR_STATE_REG_OFFSET;
    UART_STATUS_REG_OFFSET := word.of_Z UART_STATUS_REG_OFFSET;
    UART_STATUS_TXFULL_BIT := word.of_Z UART_STATUS_TXFULL_BIT;
    UART_STATUS_TXIDLE_BIT := word.of_Z UART_STATUS_TXIDLE_BIT;
    UART_WDATA_WDATA_MASK := word.of_Z UART_WDATA_WDATA_MASK;
    UART_WDATA_WDATA_OFFSET := word.of_Z UART_WDATA_WDATA_OFFSET;
    UART_WDATA_WDATA_FIELD := word.of_Z UART_WDATA_WDATA_FIELD;
    UART_WDATA_REG_OFFSET := word.of_Z UART_WDATA_REG_OFFSET;

    (* sw/device/silicon_creator/lib/drivers/uart.c *)
    NCO_WIDTH := word.of_Z NCO_WIDTH;

    (* sw/device/silicon_creator/lib/error.h *)
    kModuleUart := word.of_Z kModuleUart;
    kErrorOk := word.of_Z kErrorOk;
    kErrorUartInvalidArgument := word.of_Z kErrorUartInvalidArgument;
    kErrorUartBadBaudRate := word.of_Z kErrorUartBadBaudRate;
  |}.

(* This list includes all the constants *)
Definition uart_globals {T} {consts : uart_constants T} : list T :=
  [  TOP_EARLGREY_UART0_BASE_ADDR
    ;UART_CTRL_NCO_MASK
    ;UART_CTRL_NCO_OFFSET
    ;UART_CTRL_NCO_FIELD
    ;UART_CTRL_TX_BIT
    ;UART_CTRL_PARITY_EN_BIT
    ;UART_CTRL_REG_OFFSET
    ;UART_FIFO_CTRL_RXRST_BIT
    ;UART_FIFO_CTRL_TXRST_BIT
    ;UART_FIFO_CTRL_REG_OFFSET
    ;UART_OVRD_REG_OFFSET
    ;UART_TIMEOUT_CTRL_REG_OFFSET
    ;UART_INTR_ENABLE_REG_OFFSET
    ;UART_INTR_STATE_REG_OFFSET
    ;UART_STATUS_REG_OFFSET
    ;UART_STATUS_TXFULL_BIT
    ;UART_STATUS_TXIDLE_BIT
    ;UART_WDATA_WDATA_MASK
    ;UART_WDATA_WDATA_OFFSET
    ;UART_WDATA_WDATA_FIELD
    ;UART_WDATA_REG_OFFSET
    ;NCO_WIDTH
    ;kModuleUart
    ;kErrorOk
    ;kErrorUartInvalidArgument
    ;kErrorUartBadBaudRate
  ].

(* All register addresses for the Uart block *)
Definition uart_reg_addrs {width} {word : word.word width}
           {global_values : uart_constants word}
  : list word.rep :=
  UART_CTRL_REG_OFFSET :: UART_STATUS_REG_OFFSET ::
  UART_FIFO_CTRL_REG_OFFSET :: UART_INTR_ENABLE_REG_OFFSET ::
  UART_INTR_STATE_REG_OFFSET :: UART_WDATA_REG_OFFSET ::
  UART_OVRD_REG_OFFSET :: UART_TIMEOUT_CTRL_REG_OFFSET :: nil.

(* This class includes all the properties the Uart constants must satisfy *)
Class uart_constants_ok
      {width} {word : word width} {word_ok : word.ok word}
      (global_values : uart_constants word.rep) :=
  { addrs_unique : unique_words uart_reg_addrs;
    addrs_aligned : Forall (fun addr => word.unsigned addr mod 4 = 0) uart_reg_addrs;
    status_flags_unique_and_nonzero :
      unique_words
        ((word.of_Z 0)
            :: (map (fun flag_position => word.slu (word.of_Z 1) flag_position)
                [UART_STATUS_TXFULL_BIT
                ; UART_STATUS_TXIDLE_BIT]));
  }.
