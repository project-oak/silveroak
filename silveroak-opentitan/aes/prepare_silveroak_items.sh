#!/bin/bash

#
# Copyright 2021 The Project Oak Authors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

# Prepare generated files for OpenTitan compatiblity

set -eu

# Remove timing as OpenTitan modules do not have them and Verilator raises
# errors with mixed usage
awk '!/timeprecision/ { print }' Impl/aes_mix_columns.sv > aes_mix_columns.sv
awk '!/timeprecision/ { print }' Impl/aes_sbox_lut.sv > aes_sbox_lut.sv
awk '!/timeprecision/ { print }' Impl/aes_shift_rows.sv > aes_shift_rows.sv

# Add dummy parameters for aes_sub_bytes and aes_cipher_core
awk '
  { switch ($0) {
    case /module aes_sub_bytes/: {print "module aes_sub_bytes #( parameter SBoxImpl = \"lut\") ("}; break
    case /timeprecision/: break
    default: print; break
  } } ' Impl/aes_sub_bytes.sv > aes_sub_bytes.sv

awk '
  { switch ($0) {
    case /module aes_cipher_core/: {print "module aes_cipher_core #( parameter bit AES192Enable = 1, parameter SBoxImpl = \"lut\") ("}; break
    case /timeprecision/: break
    default: print; break
  } } ' Impl/aes_cipher_core.sv > aes_cipher_core.sv

