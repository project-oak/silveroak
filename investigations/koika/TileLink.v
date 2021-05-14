Require Import Koika.Frontend.
Require Import Koika.Std.

(* TileLink Uncached Lightweight *)

Module TLUL.
  (* Definition idx_sz := 4. *)
  (* Definition T := bits_t 16. *)
  (* Definition init := Bits.zeroes 16. *)

  (* Naming and parameter choices follow OpenTitan conventions *)
  Definition TL_AW  := 32.
  Definition TL_DW  := 32.
  Definition TL_AIW := 8.
  Definition TL_DIW := 1.
  Definition TL_DUW := 4.
  Definition TL_DBW := 4. (* (TL_DW>>3). *)
  Definition TL_SZW := 2. (* $clog2($clog2(TL_DBW)+1). *)

  (* typedef enum logic [2:0] { *)
  (*   PutFullData    = 3'h 0, *)
  (*   PutPartialData = 3'h 1, *)
  (*   Get            = 3'h 4 *)
  (* } tl_a_op_e; *)
  Definition tl_a_op_e :=
  {| enum_name := "tl_a_op_e";
     enum_members := vect_of_list ["PutFullData"; "PutPartialData"; "Get"];
     enum_bitpatterns := vect_of_list (map (Bits.of_nat 3) [0; 1; 4])
  |}.

  (* typedef enum logic [2:0] { *)
  (*   AccessAck     = 3'h 0, *)
  (*   AccessAckData = 3'h 1 *)
  (* } tl_d_op_e; *)
  Definition tl_d_op_e :=
  {| enum_name := "tl_d_op_e";
     enum_members := vect_of_list ["AccessAck"; "AccessAckData"];
     enum_bitpatterns := vect_of_list (map (Bits.of_nat 3) [0; 1])
  |}.

  (* typedef struct packed { *)
  (*   logic [6:0] rsvd1; // Reserved for future use *)
  (*   logic       parity_en; *)
  (*   logic [7:0] parity; // Use only lower TL_DBW bit *)
  (* } tl_a_user_t; *)
  Definition tl_a_user_t :=
  {| struct_name := "tl_a_user_t";
     struct_fields := [
       ("rsvd1",     bits_t 7);
       ("parity_en", bits_t 1);
       ("parity",    bits_t 8)
     ]
  |}.

  (* typedef struct packed { *)
  (*   logic                         a_valid; *)
  (*   tl_a_op_e                     a_opcode; *)
  (*   logic                  [2:0]  a_param; *)
  (*   logic  [top_pkg::TL_SZW-1:0]  a_size; *)
  (*   logic  [top_pkg::TL_AIW-1:0]  a_source; *)
  (*   logic   [top_pkg::TL_AW-1:0]  a_address; *)
  (*   logic  [top_pkg::TL_DBW-1:0]  a_mask; *)
  (*   logic   [top_pkg::TL_DW-1:0]  a_data; *)
  (*   tl_a_user_t                   a_user; *)

  (*   logic                         d_ready; *)
  (* } tl_h2d_t; *)
  Definition tl_h2d_t :=
  {| struct_name := "tl_h2d_t";
     struct_fields := [
       ("a_valid",   bits_t 1);
       ("a_opcode",  enum_t tl_a_op_e);
       ("a_param",   bits_t 3);
       ("a_size",    bits_t TL_SZW);
       ("a_source",  bits_t TL_AIW);
       ("a_address", bits_t TL_AW);
       ("a_mask",    bits_t TL_DBW);
       ("a_data",    bits_t TL_DW);
       ("a_user",    struct_t tl_a_user_t);

       ("d_ready",   bits_t 1)
     ]
  |}.

  (* typedef struct packed { *)
  (*   logic                         d_valid; *)
  (*   tl_d_op_e                     d_opcode; *)
  (*   logic                  [2:0]  d_param; *)
  (*   logic  [top_pkg::TL_SZW-1:0]  d_size; *)
  (*   logic  [top_pkg::TL_AIW-1:0]  d_source; *)
  (*   logic  [top_pkg::TL_DIW-1:0]  d_sink; *)
  (*   logic   [top_pkg::TL_DW-1:0]  d_data; *)
  (*   logic  [top_pkg::TL_DUW-1:0]  d_user; *)
  (*   logic                         d_error; *)

  (*   logic                         a_ready; *)
  (* } tl_d2h_t; *)
  Definition tl_d2h_t :=
  {| struct_name := "tl_d2h_t";
     struct_fields := [
       ("d_valid", bits_t 1);
       ("d_opcode", enum_t tl_d_op_e);
       ("d_param", bits_t 3);
       ("d_size", bits_t TL_SZW);
       ("d_source", bits_t TL_AIW);
       ("d_sink", bits_t TL_DIW);
       ("d_data", bits_t TL_DW);
       ("d_user", bits_t TL_DUW);
       ("d_error", bits_t 1);

       ("a_ready", bits_t 1)
     ]
 |}.

End TLUL.

(* TileLink Uncached Lightweight to AES register map *)
Module AesRegisterMap.
  Definition reg_sz := 22.
  Definition log_reg_sz := log2 reg_sz.

  Module RfParams <: Rf_sig.
    Definition lastIdx := reg_sz.
    Definition T := bits_t TLUL.TL_DW.
    Definition init := Bits.zero : T.
  End RfParams.

  Module RfBoolParams <: Rf_sig.
    Definition lastIdx := reg_sz.
    Definition T := bits_t 1.
    Definition init := Bits.zero : T.
  End RfBoolParams.

  Module register_values := Rf RfParams.
  Module register_bool_flag := Rf RfBoolParams.

  Inductive reg_t :=
  (* aes interface registers *)
  | regs (r: register_values.reg_t)
  (* signal read/write from host *)
  | read_dirty (r: register_bool_flag.reg_t)
  | write_dirty (r: register_bool_flag.reg_t)

  (* tlul packet handling registers *)
  | outstanding
  | rspop
  | reqsz
  | reqid
  | rdata
  | error
  .

  Definition R r :=
    match r with
    | regs r => register_values.R r
    | read_dirty r => register_bool_flag.R r
    | write_dirty r => register_bool_flag.R r

    | outstanding => bits_t 1
    | rspop => enum_t TLUL.tl_d_op_e
    | reqsz => bits_t TLUL.TL_SZW
    | reqid => bits_t TLUL.TL_AIW
    | rdata => bits_t TLUL.TL_DW
    | error => bits_t 1
    end.

  Definition r idx: R idx :=
    match idx with
    | regs x => register_values.r x
    | read_dirty x => register_bool_flag.r x
    | write_dirty x => register_bool_flag.r x

    | outstanding => Bits.zero
    | rspop => Bits.zero
    | reqsz => Bits.zero
    | reqid => Bits.zero
    | rdata => Bits.zero
    | error => Bits.zero
    end.

    Definition REG_AES_KEY0 := Bits.of_nat log_reg_sz 0.
    Definition REG_AES_KEY1 := Bits.of_nat log_reg_sz 1.
    Definition REG_AES_KEY2 := Bits.of_nat log_reg_sz 2.
    Definition REG_AES_KEY3 := Bits.of_nat log_reg_sz 3.
    Definition REG_AES_KEY4 := Bits.of_nat log_reg_sz 4.
    Definition REG_AES_KEY5 := Bits.of_nat log_reg_sz 5.
    Definition REG_AES_KEY6 := Bits.of_nat log_reg_sz 6.
    Definition REG_AES_KEY7 := Bits.of_nat log_reg_sz 7.
    Definition REG_AES_IV0 := Bits.of_nat log_reg_sz 8.
    Definition REG_AES_IV1 := Bits.of_nat log_reg_sz 9.
    Definition REG_AES_IV2 := Bits.of_nat log_reg_sz 10.
    Definition REG_AES_IV3 := Bits.of_nat log_reg_sz 11.
    Definition REG_AES_DATA_IN0 := Bits.of_nat log_reg_sz 12.
    Definition REG_AES_DATA_IN1 := Bits.of_nat log_reg_sz 13.
    Definition REG_AES_DATA_IN2 := Bits.of_nat log_reg_sz 14.
    Definition REG_AES_DATA_IN3 := Bits.of_nat log_reg_sz 15.
    Definition REG_AES_DATA_OUT0 := Bits.of_nat log_reg_sz 16.
    Definition REG_AES_DATA_OUT1 := Bits.of_nat log_reg_sz 17.
    Definition REG_AES_DATA_OUT2 := Bits.of_nat log_reg_sz 18.
    Definition REG_AES_DATA_OUT3 := Bits.of_nat log_reg_sz 19.
    Definition REG_AES_CTRL := Bits.of_nat log_reg_sz 20.
    Definition REG_AES_TRIGGER := Bits.of_nat log_reg_sz 21.
    Definition REG_AES_STATUS := Bits.of_nat log_reg_sz 22.

  Definition aes_register_name {n} (v: Vect.index n) :=
    match index_to_nat v with
    |  0 => "AES_KEY0"
    |  1 => "AES_KEY1"
    |  2 => "AES_KEY2"
    |  3 => "AES_KEY3"
    |  4 => "AES_KEY4"
    |  5 => "AES_KEY5"
    |  6 => "AES_KEY6"
    |  7 => "AES_KEY7"
    |  8 => "AES_IV0"
    |  9 => "AES_IV1"
    | 10 => "AES_IV2"
    | 11 => "AES_IV3"
    | 12 => "AES_DATA_IN0"
    | 13 => "AES_DATA_IN1"
    | 14 => "AES_DATA_IN2"
    | 15 => "AES_DATA_IN3"
    | 16 => "AES_DATA_OUT0"
    | 17 => "AES_DATA_OUT1"
    | 18 => "AES_DATA_OUT2"
    | 19 => "AES_DATA_OUT3"
    | 20 => "AES_CTRL"
    | 21 => "AES_TRIGGER"
    | 22 => "AES_STATUS"
    | _ => "Bad register index"
    end.

  (* Process TLUL packets, based on
     https://github.com/lowRISC/opentitan/blob/19044edfb0b9485031557705595840bea41fb33d/hw/ip/tlul/rtl/tlul_adapter_reg.sv *)

  Definition outgoing_tlul_packet : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun outgoing_tlul_packet () : struct_t TLUL.tl_d2h_t =>
       let curr_outstanding := read0(outstanding) in

       struct TLUL.tl_d2h_t {
           a_ready := !curr_outstanding;
           d_valid := curr_outstanding;
           d_opcode := read0(rspop);
           d_param := Ob~0~0~0;
           d_size := read0(reqsz);
           d_source := read0(reqid);
           d_sink := Ob~0;
           d_data := read0(rdata);
           d_user := Ob~0~0~0~0;
           d_error := read0(error)
         }
    }}.

  Definition incoming_tlul_packet : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun incoming_tlul_packet (tl_i: struct_t TLUL.tl_h2d_t) : unit_t =>
       let curr_outstanding := read0(outstanding) in

       let a_ack := get(tl_i, a_valid) && !curr_outstanding in
       let d_ack := curr_outstanding && get(tl_i, d_ready) in

       let rd_req := a_ack && (get(tl_i, a_opcode) == enum TLUL.tl_a_op_e { Get } ) in
       let wr_req := a_ack && (
         get(tl_i, a_opcode) == enum TLUL.tl_a_op_e { PutFullData } ||
         get(tl_i, a_opcode) == enum TLUL.tl_a_op_e { PutPartialData }
       ) in

       (* TODO(blaxill): skipping malformed tl packet detection *)
       let err_internal := Ob~0 in
       let error_i := Ob~0 in

       if a_ack then (
         write0(reqid, get(tl_i, a_source));
         write0(reqsz, get(tl_i, a_size));
         write0(rspop,
           if rd_req then enum TLUL.tl_d_op_e { AccessAckData }
           else enum TLUL.tl_d_op_e { AccessAck });
         write0(error, error_i || err_internal);

         write0(outstanding, Ob~1)
       )
       else if d_ack then write0(outstanding, Ob~0)
       else pass;

       let we_o := wr_req && !err_internal in
       let re_o := rd_req && !err_internal in

       let wdata_o := get(tl_i, a_data) in
       let be_o    := get(tl_i, a_mask) in
       let reg_idx := get(tl_i, a_address)[|5`d2| :+ 5] in

       if we_o then (
         regs.(register_values.write)(reg_idx, wdata_o);
         write_dirty.(register_bool_flag.write)(reg_idx, Ob~1)
       ) else pass;

       if re_o then (
         let val := regs.(register_values.read)(reg_idx) in
         read_dirty.(register_bool_flag.write)(reg_idx, Ob~1);
         write0(rdata, val)
       ) else pass
    }}.

  Definition read : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun read (idx : bits_t (log2 RfParams.lastIdx)) : bits_t 32 =>
       regs.(register_values.read)(idx)
    }}.

  Definition write : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun write (idx : bits_t (log2 RfParams.lastIdx)) (val: bits_t 32) : unit_t =>
       regs.(register_values.write)(idx, val)
    }}.

  Definition is_write_dirty : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun is_write_dirty (idx : bits_t (log2 RfParams.lastIdx)) : bits_t 1 =>
       write_dirty.(register_bool_flag.read)(idx)
    }}.

  Definition is_read_dirty : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun is_read_dirty (idx : bits_t (log2 RfParams.lastIdx)) : bits_t 1 =>
       read_dirty.(register_bool_flag.read)(idx)
    }}.

  Definition clear_flags : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun clear_flags (idx : bits_t (log2 RfParams.lastIdx)) : unit_t =>
       read_dirty.(register_bool_flag.write)(idx, Ob~0);
       write_dirty.(register_bool_flag.write)(idx, Ob~0)
    }}.

  Definition clear_all_flags : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun clear_all_flags () : unit_t =>
       `USugar
        (UProgn
          (List.map
            (fun idx => {{ clear_flags( #(Bits.of_nat (log2 RfParams.lastIdx) idx) ) }})
            (List.seq 0 RfParams.lastIdx)
          )) `
    }}.

End AesRegisterMap.
