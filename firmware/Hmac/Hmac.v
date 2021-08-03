(* Note: This code does not compute any HMAC, but it uses the
   opentitan HMAC module to compute SHA-256 sums. *)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.
Import Syntax.Coercions List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Require Import Bedrock2Experiments.LibBase.AbsMMIO.
Require Import Bedrock2Experiments.LibBase.Bitfield.
Require Import Bedrock2Experiments.LibBase.Constants.
Require Import Bedrock2Experiments.Hmac.Constants.

Local Notation "0" := (expr.literal 0) (in custom bedrock_expr).
Local Notation "1" := (expr.literal 1) (in custom bedrock_expr).
Local Notation "2" := (expr.literal 2) (in custom bedrock_expr).
Local Notation "3" := (expr.literal 3) (in custom bedrock_expr).
Local Notation "4" := (expr.literal 4) (in custom bedrock_expr).
Local Notation "5" := (expr.literal 5) (in custom bedrock_expr).
Local Notation "6" := (expr.literal 6) (in custom bedrock_expr).
Local Notation "7" := (expr.literal 7) (in custom bedrock_expr).
Local Notation "8" := (expr.literal 8) (in custom bedrock_expr).
Local Notation "9" := (expr.literal 9) (in custom bedrock_expr).

Local Notation true := 1.
Local Notation false := 0.

Definition UINT32_MAX: Z := 2 ^ 32 - 1.

(*
void hmac_sha256_init(void) {
  // Clear the config, stopping the SHA engine.
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CFG_REG_OFFSET, 0u);

  // Disable and clear interrupts. INTR_STATE register is rw1c.
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_INTR_ENABLE_REG_OFFSET,
                   0u);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_INTR_STATE_REG_OFFSET,
                   UINT32_MAX);

  uint32_t reg = 0;
  reg = bitfield_bit32_write(reg, HMAC_CFG_DIGEST_SWAP_BIT, false);
  // Enable endian swap since our inputs are little-endian.
  reg = bitfield_bit32_write(reg, HMAC_CFG_ENDIAN_SWAP_BIT, true);
  reg = bitfield_bit32_write(reg, HMAC_CFG_SHA_EN_BIT, true);
  reg = bitfield_bit32_write(reg, HMAC_CFG_HMAC_EN_BIT, false);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CFG_REG_OFFSET, reg);

  reg = 0;
  reg = bitfield_bit32_write(reg, HMAC_CMD_HASH_START_BIT, true);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CMD_REG_OFFSET, reg);
}
*)
Definition b2_hmac_sha256_init: func :=
  let reg := "reg" in
  ("b2_hmac_sha256_init",
   ([], [], bedrock_func_body:(
     (* Clear the config, stopping the SHA engine. *)
     (* Note: the above comment might be misleading: if the SHA engine is running,
        writes to the CFG register are discarded, says the doc *)
     abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CFG_REG_OFFSET, 0);

     (* Disable and clear interrupts. INTR_STATE register is rw1c. *)
     abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_INTR_ENABLE_REG_OFFSET, 0);
     abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_INTR_STATE_REG_OFFSET, UINT32_MAX);

     reg = 0;
     unpack! reg = bitfield_bit32_write(reg, HMAC_CFG_DIGEST_SWAP_BIT, false);
     (* Enable endian swap since our inputs are little-endian. *)
     unpack! reg = bitfield_bit32_write(reg, HMAC_CFG_ENDIAN_SWAP_BIT, true);
     unpack! reg = bitfield_bit32_write(reg, HMAC_CFG_SHA_EN_BIT, true);
     unpack! reg = bitfield_bit32_write(reg, HMAC_CFG_HMAC_EN_BIT, false);
     abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CFG_REG_OFFSET, reg);

     reg = 0;
     unpack! reg = bitfield_bit32_write(reg, HMAC_CMD_HASH_START_BIT, true);
     abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CMD_REG_OFFSET, reg)
  ))).


(*
rom_error_t hmac_sha256_update(const void *data, size_t len) {
  if (data == NULL) {
    return kErrorHmacInvalidArgument;
  }
  const uint8_t *data_sent = ( const uint8_t * )data;

  // Individual byte writes are needed if the buffer isn't word aligned.
  for (; len != 0 && (uintptr_t)data_sent & 3; --len) {
    abs_mmio_write8(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_MSG_FIFO_REG_OFFSET,
                    *data_sent++);
  }

  for (; len >= sizeof(uint32_t); len -= sizeof(uint32_t)) {
    // FIXME: read_32 does not work for unittests.
    uint32_t data_aligned = *( const uint32_t * )data_sent;
    abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_MSG_FIFO_REG_OFFSET,
                     data_aligned);
    data_sent += sizeof(uint32_t);
  }

  // Handle non-32bit aligned bytes at the end of the buffer.
  for (; len != 0; --len) {
    abs_mmio_write8(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_MSG_FIFO_REG_OFFSET,
                    *data_sent++);
  }
  return kErrorOk;
}
*)
(* Note: only works if x is 0 or 1! *)
Local Notation "'NOT' ( x ) " := (expr.op bopname.sub 1 x)
  (x custom bedrock_expr, in custom bedrock_expr at level 0).

Definition b2_hmac_sha256_update: func :=
  let data := "data" in
  let len := "len" in
  let result := "result" in
  let data_sent := "data_sent" in
  let data_aligned := "data_aligned" in
  ("b2_hmac_sha256_update",
   ([data; len], [result], bedrock_func_body:(
     if (data == 0) {
       result = kErrorHmacInvalidArgument
     } else {
       data_sent = data;

       (* Individual byte writes are needed if the buffer isn't word aligned. *)
       (* TODO support for negation and != *)
       while (NOT(len == 0) & NOT((data_sent & 3) == 0)) {
         abs_mmio_write8(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_MSG_FIFO_REG_OFFSET, load1(data_sent));
         data_sent = data_sent + 1;
         len = len - 1
       };

       (* TODO support <=, >=, >, maybe also signed? *)
       while (3 < len) {
         data_aligned = load4(data_sent);
         abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_MSG_FIFO_REG_OFFSET, data_aligned);
         data_sent = data_sent + 4;
         len = len - 4
       };

       (* Handle non-32bit aligned bytes at the end of the buffer. *)
       while (len) {
         abs_mmio_write8(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_MSG_FIFO_REG_OFFSET, load1(data_sent));
         data_sent = data_sent + 1;
         len = len - 1
       };
       result = kErrorOk
     }
  ))).


(*
rom_error_t hmac_sha256_final(hmac_digest_t *digest) {
  if (digest == NULL) {
    return kErrorHmacInvalidArgument;
  }

  uint32_t reg = 0;
  reg = bitfield_bit32_write(reg, HMAC_CMD_HASH_PROCESS_BIT, true);
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CMD_REG_OFFSET, reg);

  do {
    reg = abs_mmio_read32(TOP_EARLGREY_HMAC_BASE_ADDR +
                          HMAC_INTR_STATE_REG_OFFSET);
  } while (!bitfield_bit32_read(reg, HMAC_INTR_STATE_HMAC_DONE_BIT));
  abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_INTR_STATE_REG_OFFSET,
                   reg);

  // Read the digest in reverse to preserve the numerical value.
  // The least significant word is at HMAC_DIGEST_7_REG_OFFSET.
  for (size_t i = 0; i < ARRAYSIZE(digest->digest); ++i) {
    digest->digest[i] =
        abs_mmio_read32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_DIGEST_7_REG_OFFSET -
                        (i * sizeof(uint32_t)));
  }
  return kErrorOk;
}
*)
Definition b2_hmac_sha256_final: func :=
  let digest := "digest" in
  let result := "result" in
  let reg := "reg" in
  let done := "done" in
  let i := "i" in
  let temp := "temp" in
  ("b2_hmac_sha256_final",
   ([digest], [result], bedrock_func_body:(
     if (digest == 0) {
       result = kErrorHmacInvalidArgument
     } else {
       reg = 0;
       unpack! reg = bitfield_bit32_write(reg, HMAC_CMD_HASH_PROCESS_BIT, true);
       abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_CMD_REG_OFFSET, reg);

       done = 0;
       while (NOT(done)) { (* <-- TODO support boolean negation *)
         unpack! reg = abs_mmio_read32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_INTR_STATE_REG_OFFSET);
         unpack! done = bitfield_bit32_read(reg, HMAC_INTR_STATE_HMAC_DONE_BIT)
       };
       abs_mmio_write32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_INTR_STATE_REG_OFFSET, reg);

       (* Read the digest in reverse to preserve the numerical value. *)
       (* The least significant word is at HMAC_DIGEST_7_REG_OFFSET. *)
       i = 0;
       while (i < 8) {
         unpack! temp = abs_mmio_read32(TOP_EARLGREY_HMAC_BASE_ADDR + HMAC_DIGEST_7_REG_OFFSET -
                             (i * 4));
         store4(digest + i * 4, temp);
         i = i + 1
       };
       result = kErrorOk
     }
   ))).
