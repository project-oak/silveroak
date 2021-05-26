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

  (* Enum option definitions from dif_uart.h *)
  kDifUartInterruptTxWatermark  : T; (* dif_uart_interrupt enum value *)
  kDifUartInterruptRxWatermark  : T; (* dif_uart_interrupt enum value *)
  kDifUartInterruptTxEmpty      : T; (* dif_uart_interrupt enum value *)
  kDifUartInterruptRxOverflow   : T; (* dif_uart_interrupt enum value *)
  kDifUartInterruptRxFrameErr   : T; (* dif_uart_interrupt enum value *)
  kDifUartInterruptRxBreakErr   : T; (* dif_uart_interrupt enum value *)
  kDifUartInterruptRxTimeout    : T; (* dif_uart_interrupt enum value *)
  kDifUartInterruptRxParityErr  : T; (* dif_uart_interrupt enum value *)
  kDifUartInterruptLast         : T; (* dif_uart_interrupt enum value *)
  kDifUartWatermarkByte1        : T; (* dif_uart_watermark enum value *)
  kDifUartWatermarkByte4        : T; (* dif_uart_watermark enum value *)
  kDifUartWatermarkByte8        : T; (* dif_uart_watermark enum value *)
  kDifUartWatermarkByte16       : T; (* dif_uart_watermark enum value *)
  kDifUartWatermarkByte30       : T; (* dif_uart_watermark enum value *)
  kDifUartWatermarkLast         : T; (* dif_uart_watermark enum value *)
  kDifUartEnable                : T; (* dif_uart_enable enum value *)
  kDifUartDisable               : T; (* dif_uart_enable enum value *)
  kDifUartParityOdd             : T; (* dif_uart_parity enum value *)
  kDifUartParityEven            : T; (* dif_uart_parity enum value *)
  kDifUartOk                    : T; (* dif_uart_result enum value *)
  kDifUartError                 : T; (* dif_uart_result enum value *)
  kDifUartBadArg                : T; (* dif_uart_result enum value *)
  kDifUartConfigOk              : T; (* dif_uart_config_result enum value *)
  kDifUartConfigError           : T; (* dif_uart_config_result enum value *)
  kDifUartConfigBadArg          : T; (* dif_uart_config_result enum value *)
  kDifUartConfigBadConfig       : T; (* dif_uart_config_result enum value *)
  kDifUartConfigBadNco          : T; (* dif_uart_config_result enum value *)
  }.

(* Given the string names of all constants, coerce them to bedroc2
   expressions with expr.var *)
Definition constant_vars
           {names : uart_constants string}
  : uart_constants expr :=
  {|
    kDifUartInterruptTxWatermark   := expr.var kDifUartInterruptTxWatermark;
    kDifUartInterruptRxWatermark   := expr.var kDifUartInterruptRxWatermark;
    kDifUartInterruptTxEmpty       := expr.var kDifUartInterruptTxEmpty;
    kDifUartInterruptRxOverflow    := expr.var kDifUartInterruptRxOverflow;
    kDifUartInterruptRxFrameErr    := expr.var kDifUartInterruptRxFrameErr;
    kDifUartInterruptRxBreakErr    := expr.var kDifUartInterruptRxBreakErr;
    kDifUartInterruptRxTimeout     := expr.var kDifUartInterruptRxTimeout;
    kDifUartInterruptRxParityErr   := expr.var kDifUartInterruptRxParityErr;
    kDifUartInterruptLast          := expr.var kDifUartInterruptLast;
    kDifUartWatermarkByte1         := expr.var kDifUartWatermarkByte1;
    kDifUartWatermarkByte4         := expr.var kDifUartWatermarkByte4;
    kDifUartWatermarkByte8         := expr.var kDifUartWatermarkByte8;
    kDifUartWatermarkByte16        := expr.var kDifUartWatermarkByte16;
    kDifUartWatermarkByte30        := expr.var kDifUartWatermarkByte30;
    kDifUartWatermarkLast          := expr.var kDifUartWatermarkLast;
    kDifUartEnable                 := expr.var kDifUartEnable;
    kDifUartDisable                := expr.var kDifUartDisable;
    kDifUartParityOdd              := expr.var kDifUartParityOdd;
    kDifUartParityEven             := expr.var kDifUartParityEven;
    kDifUartOk                     := expr.var kDifUartOk;
    kDifUartError                  := expr.var kDifUartError;
    kDifUartBadArg                 := expr.var kDifUartBadArg;
    kDifUartConfigOk               := expr.var kDifUartConfigOk;
    kDifUartConfigError            := expr.var kDifUartConfigError;
    kDifUartConfigBadArg           := expr.var kDifUartConfigBadArg;
    kDifUartConfigBadConfig        := expr.var kDifUartConfigBadConfig;
    kDifUartConfigBadNco           := expr.var kDifUartConfigBadNco;
  |}.

(* This instance provide the string name for each constant *)
Definition constant_names : uart_constants string :=
  {|
    kDifUartInterruptTxWatermark := "kDifUartInterruptTxWatermark";
    kDifUartInterruptRxWatermark := "kDifUartInterruptRxWatermark";
    kDifUartInterruptTxEmpty := "kDifUartInterruptTxEmpty";
    kDifUartInterruptRxOverflow := "kDifUartInterruptRxOverflow";
    kDifUartInterruptRxFrameErr := "kDifUartInterruptRxFrameErr";
    kDifUartInterruptRxBreakErr := "kDifUartInterruptRxBreakErr";
    kDifUartInterruptRxTimeout := "kDifUartInterruptRxTimeout";
    kDifUartInterruptRxParityErr := "kDifUartInterruptRxParityErr";
    kDifUartInterruptLast := "kDifUartInterruptLast";
    kDifUartWatermarkByte1 := "kDifUartWatermarkByte1";
    kDifUartWatermarkByte4 := "kDifUartWatermarkByte4";
    kDifUartWatermarkByte8 := "kDifUartWatermarkByte8";
    kDifUartWatermarkByte16 := "kDifUartWatermarkByte16";
    kDifUartWatermarkByte30 := "kDifUartWatermarkByte30";
    kDifUartWatermarkLast := "kDifUartWatermarkLast";
    kDifUartEnable := "kDifUartEnable";
    kDifUartDisable := "kDifUartDisable";
    kDifUartParityOdd := "kDifUartParityOdd";
    kDifUartParityEven := "kDifUartParityEven";
    kDifUartOk := "kDifUartOk";
    kDifUartError := "kDifUartError";
    kDifUartBadArg := "kDifUartBadArg";
    kDifUartConfigOk := "kDifUartConfigOk";
    kDifUartConfigError := "kDifUartConfigError";
    kDifUartConfigBadArg := "kDifUartConfigBadArg";
    kDifUartConfigBadConfig := "kDifUartConfigBadConfig";
    kDifUartConfigBadNco := "kDifUartConfigBadNco";
 |}.
