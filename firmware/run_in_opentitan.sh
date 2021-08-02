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

OT_hash=$(git ls-files -s ../../third_party/opentitan/ | awk '{print $2}')
echo "third_party/opentitan is at commit $OT_hash"

if [[ $OT_hash != "783edaf444eb0d9eaf9df71c785089bffcda574e" ]]; then
  read -p "We expect commit 783edaf444eb0d9eaf9df71c785089bffcda574e, do you want to continue? (y/N) " cont
  case $cont in
    [Yy]* ) ;;
    * ) exit ;;
  esac
fi

# ensures aes.c is fresh
make aes.c

# copy aes.c to opentitan
cp aes.c ../../third_party/opentitan/sw/device/lib/aes.c

cd ../../third_party/opentitan

./meson_init.sh

fusesoc --cores-root . run --flag=fileset_top --target=sim --setup --build lowrisc:systems:top_earlgrey_verilator

# remove uart0.log if it exists (so we don't read old data by accident)
rm -f uart0.log

# build the boot rom and AES tests
ninja -C build-out sw/device/boot_rom/boot_rom_export_sim_verilator
ninja -C build-out sw/device/tests/aes_test_export_sim_verilator

# The simulator won't automatically terminate so we use bash to sleep and then
# kill the process
(build/lowrisc_systems_top_earlgrey_verilator_0.1/sim-verilator/Vtop_earlgrey_verilator --meminit=rom,build-bin/sw/device/boot_rom/boot_rom_sim_verilator.elf --meminit=flash,build-bin/sw/device/tests/aes_test_sim_verilator.elf) & sleep 15 ; kill -2 $!
wait

cat uart0.log
