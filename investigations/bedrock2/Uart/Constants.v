Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import coqutil.Word.Interface.
Require Import Bedrock2Experiments.Word.
Require Import Bedrock2Experiments.ConstantFields.

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
    UART_INTR_TEST_REG_OFFSET     : T;
    UART_STATUS_REG_OFFSET        : T;
    UART_STATUS_TXFULL_BIT        : T;
    UART_STATUS_TXIDLE_BIT        : T;
    UART_WDATA_WDATA_MASK         : T;
    UART_WDATA_WDATA_OFFSET       : T;
    UART_WDATA_WDATA_FIELD        : T;
    UART_WDATA_REG_OFFSET         : T;
    UART_RDATA_REG_OFFSET         : T;
    UART_VAL_REG_OFFSET           : T;
    UART_FIFO_STATUS_REG_OFFSET   : T;

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
Definition constant_vars {names : uart_constants string} : uart_constants expr :=
  ltac:(map_record_fields expr.var).

(* Given the Z values of all the constants, coerce them to bedrock2
   expressionswith expr.literal *)
Definition constant_literals {vals : uart_constants Z} : uart_constants expr :=
  ltac:(map_record_fields expr.literal).

(* This instance provide the string name for each constant *)
Definition constant_names : uart_constants string :=
  ltac:(instantiate_record_with_fieldname_vars).

Ltac app_to_string_list a :=
  match a with
  | ?f ?x => match type of x with
             | string => let r := app_to_string_list f in constr:(x :: r)
             end
  | _ => constr:(@nil string)
  end.

(* This list includes all the constants *)
Definition uart_globals: list string.
  let a := eval unfold constant_names in constant_names in
  let r := app_to_string_list a in exact r.
Defined.

(* All register addresses for the Uart block *)
Definition uart_reg_addrs {width} {word : word.word width}
           {global_values : uart_constants Z}
  : list word :=
  let base := TOP_EARLGREY_UART0_BASE_ADDR in
  map (fun var => word.of_Z (base + var)) [
    UART_INTR_STATE_REG_OFFSET
    ; UART_INTR_ENABLE_REG_OFFSET
    ; UART_INTR_TEST_REG_OFFSET
    ; UART_CTRL_REG_OFFSET
    ; UART_STATUS_REG_OFFSET
    ; UART_RDATA_REG_OFFSET
    ; UART_WDATA_REG_OFFSET
    ; UART_FIFO_CTRL_REG_OFFSET
    ; UART_FIFO_STATUS_REG_OFFSET
    ; UART_OVRD_REG_OFFSET
    ; UART_VAL_REG_OFFSET
    ; UART_TIMEOUT_CTRL_REG_OFFSET
  ].

(* see https://github.com/mit-plv/bedrock2/pull/180 *)
#[export] Hint Mode word.word - : typeclass_instances.

(* This class includes all the properties the Uart constants must satisfy *)
Class uart_constants_ok
      {width} {word : word width} {word_ok : word.ok word}
      (global_values : uart_constants Z) :=
  { addrs_unique : NoDup uart_reg_addrs;
    addrs_aligned : Forall (fun addr => word.unsigned addr mod 4 = 0) uart_reg_addrs;
    addrs_small : Forall (fun addr => word.unsigned addr + 4 <= 2 ^ width) uart_reg_addrs;

    status_flags_unique_and_nonzero :
      NoDup
        ((word.of_Z 0)
            :: (map (fun flag_position => word.slu (word.of_Z 1) (word.of_Z flag_position))
                [UART_STATUS_TXFULL_BIT
                ; UART_STATUS_TXIDLE_BIT]));
  }.
