OPENTITAN_AES_DIR=../../third_party/opentitan/hw/ip/aes/rtl
VERILATOR_CONFIG=../../third_party/opentitan/hw/lint/tools/verilator/common.vlt

# Comment out timing
awk '{ if ($0 ~ /timeprecision/) { print "/*" $0 "*/" } else { print $0 } }' Acorn/aes_mix_columns.sv > aes_mix_columns.sv
awk '{ if ($0 ~ /timeprecision/) { print "/*" $0 "*/" } else { print $0 } }' Acorn/aes_sbox_lut.sv > aes_sbox_lut.sv
awk '{ if ($0 ~ /timeprecision/) { print "/*" $0 "*/" } else { print $0 } }' Acorn/aes_shift_rows.sv > aes_shift_rows.sv

# For aes_sub_bytes additionally add a dummy parameter to module definition
awk '{ \
  if ($0 ~ /module aes_sub_bytes/) {print "module aes_sub_bytes #( parameter SBoxImpl = \"lut\") ("} \
  else { \
    if ($0 ~ /timeprecision/) { print "/*" $0 "*/" } else { print $0 } \
  } }' Acorn/aes_sub_bytes.sv > aes_sub_bytes.sv

cp aes_mix_columns.sv aes_sbox_lut.sv aes_sub_bytes.sv aes_shift_rows.sv $OPENTITAN_AES_DIR

# OpenTitan Verilator is empty, we need to turn off "DETECTARRAYS" as we
# generate large arrays that choke this Verilator pass. Alternatively we could
# rebuild Verilator with larger inbuilt DETECTARRAYS constant
cat <<EOS > $VERILATOR_CONFIG
\`verilator_config
lint_off -rule DETECTARRAY
EOS

