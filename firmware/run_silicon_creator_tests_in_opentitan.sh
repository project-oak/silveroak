#!/bin/bash

# Note: this script should be run in a recent checkout of opentitan (silveroak's opentitan submodule is too old).
# Tested on Sam's machine using commit 6acb77994f07c443347f3a3c34a8df334dc11f43 from Mon Jun 7 22:12:15 2021 -0700
# It also assumes that the following one-time-setup commands have already been run:
#
# pip3 install --user -r python-requirements.txt # they changed, so it's not sufficient to have run this in the outdated opentitan submodule of silveroak
# ./meson_init.sh
# fusesoc --cores-root . run --flag=fileset_top --target=sim --setup --build lowrisc:systems:chip_earlgrey_verilator # "top" has been renamed to "chip"
#
set -eu

if [ $# -eq 0 ]
then
	echo "Provide the name of the driver (e.g., uart) to test"
	exit
fi

DEVICE_NAME=$1

# this script lives in silveroak/firmware, so we can rely on ${BASH_SOURCE[0]} to find that directory
BEDROCK2_EXPERIMENTS="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"

make -C $BEDROCK2_EXPERIMENTS

cp $BEDROCK2_EXPERIMENTS/${DEVICE_NAME}.c.out sw/device/silicon_creator/lib/drivers/${DEVICE_NAME}.c

ninja -C build-out all

# unit tests:
ninja -C build-out test

# functional test:
# skip if functional test does not exist
FUNCTEST=build-bin/sw/device/silicon_creator/testing/sw_silicon_creator_lib_driver_${DEVICE_NAME}_functest_sim_verilator.elf

if [ ! -f ${FUNCTEST} ]
then
	echo "No functional test for ${DEVICE_NAME}. Skipping"
	exit
fi

build/lowrisc_systems_chip_earlgrey_verilator_0.1/sim-verilator/Vchip_earlgrey_verilator \
    --meminit=rom,build-bin/sw/device/boot_rom/boot_rom_sim_verilator.scr.40.vmem \
    --meminit=otp,build-bin/sw/device/otp_img/otp_img_sim_verilator.vmem \
    --meminit=flash,${FUNCTEST}
