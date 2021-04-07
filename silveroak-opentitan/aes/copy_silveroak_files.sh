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

set -eu

BASE_DIR=${1:-../../third_party/opentitan}
BASE_DIR+=/hw/ip/aes/rtl

cp aes_mix_columns.sv aes_sbox_lut.sv aes_sub_bytes.sv aes_shift_rows.sv aes_cipher_core.sv $BASE_DIR
