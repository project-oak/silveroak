# Prerequisites 

1. Run `make` at the top level to make sure `third_party` submodules are
   populated and the SilverOak AES is built.

## Install OpenTitan tool dependencies 

Follow the steps at https://docs.opentitan.org/doc/ug/install_instructions/#compiler-toolchain
to build the compiler toolchain. The OpenTitan notes install to `/tools` but as
long as the correct binaries are on your `$PATH` it may not matter. Note: 
- The Verible link has an extra `v` and the correct command is 
  ```
  wget https://github.com/google/verible/releases/download/${VERIBLE_VERSION}/verible-${VERIBLE_VERSION}-Ubuntu-18.04-bionic-x86_64.tar.gz
  ```
- Vivado is not needed if you only want to simulate with Verilator.

## Build software

```
./meson_init.sh
ninja -C build-out all
```

### If the software build fails with 'fti_*' deprecation error

e.g.

```
../sw/host/vendor/mpsse/support.c:63:8: error: ‘ftdi_usb_purge_rx_buffer’ is deprecated
```

Edit the meson build file to disable ftdi deprecation warnings.

```
vim sw/host/vendor/meson.build
```

Add '-D_FTDI_DISABLE_DEPRECATED' to the c_args list:

```

    c_args: [
      '-I' + meson.source_root() + '/sw/host/vendor/mpsse',
      '-D_FTDI_DISABLE_DEPRECATED'
    ],
```

## Replace the combinational components

1. Make sure the SilverOak AES components were built by the first step.
1. Then whilst in the `silveroak-opentitan/aes` directory run
   `./copy_silveroak_files.sh`
1. The SilverOak components should now be in `third_party/opentitan/hw/ip/aes/rtl/`

## Build the OpenTitan Verilator model

1. Navigate to third_party/opentitan, and run fusesoc:

```
fusesoc --cores-root . run --flag=fileset_top --target=sim --setup --build lowrisc:systems:top_earlgrey_verilator
```

## Run the aes_test.c (simulation)

`aes_test.c` is a basic test case in the OpenTitan project for AES, it can be
run by calling:

```
build/lowrisc_systems_top_earlgrey_verilator_0.1/sim-verilator/Vtop_earlgrey_verilator \
  --meminit=rom,build-bin/sw/device/boot_rom/boot_rom_sim_verilator.elf \
  --meminit=flash,build-bin/sw/device/tests/aes_test_sim_verilator.elf \
  '+UARTDPI_LOG_uart0=-'
```

(Note: This should emit uart output to console, but perhaps only with newer
versions)

After 5-10 seconds the simulation can be canceled via `C^`. A file `uart0.log`
should have been created and should note where `aes_test.c` succeeded or failed.

## Run the baseline aes_test.c (on the actual Nexys Video FPGA board)

First this is how to build and run the baseline AES `aes_test.c` on the FPGA board
i.e. the version from OpenTitan without any of our modifications. We use commands
that work with the older version of the OpenTitan codebase we work with.

### Build the FPGA bitsream
This step requires the installation of the Xilinx Vivado FPGA desingn tools. From the `silveroak/third_party/opentitan` sub-directory do:
```console
$ ./meson_init.sh
$ ninja -C build-out sw/device/boot_rom/boot_rom_export_fpga_nexysvideo
$ fusesoc --cores-root . run --target=synth lowrisc:systems:top_earlgrey_nexysvideo
```

This build an FPGA image for the OpenTitan design which wakes up and runs a bootloader program. Plug in the FPGA board and work out which device the UART from the FPGA is plugged into and use the `screen` command to connect to it e.g.
```console
$ sudo screen /dev/ttyUSB2 230400
```

Program the FPGA board:
```console
$ fusesoc --cores-root . pgm lowrisc:systems:top_earlgrey_nexysvideo:0.1
WARNING: Unknown item formal in section Target
WARNING: Unknown item formal in section Target
WARNING: The 'pgm' subcommand is deprecated and will be removed in the next release. Use 'fusesoc run --target=synth --run' instead.
INFO: Running
export HW_TARGET=; \
export JTAG_FREQ=; \
vivado -quiet -nolog -notrace -mode batch -source lowrisc_systems_top_earlgrey_nexysvideo_0.1_pgm.tcl -tclargs xc7a200tsbg484-1 lowrisc_systems_top_earlgrey_nexysvideo_0.1.bit
WARNING: Default location for XILINX_VIVADO_HLS not found: 
FuseSoC Xilinx FPGA Programming Tool
====================================

INFO: Programming part xc7a200tsbg484-1 with bitstream lowrisc_systems_top_earlgrey_nexysvideo_0.1.bit
INFO: [Labtools 27-2285] Connecting to hw_server url TCP:localhost:3121
INFO: [Labtools 27-2222] Launching hw_server...
INFO: [Labtools 27-2221] Launch Output:

****** Xilinx hw_server v2018.3
  **** Build date : Dec  6 2018-23:53:53
    ** Copyright 1986-2018 Xilinx, Inc. All Rights Reserved.


INFO: Trying to use hardware target localhost:3121/xilinx_tcf/Digilent/210276AC80A2
INFO: [Labtoolstcl 44-466] Opening hw_target localhost:3121/xilinx_tcf/Digilent/210276AC80A2
INFO: Opened hardware target localhost:3121/xilinx_tcf/Digilent/210276AC80A2 on try 1.
INFO: Part not found as part of localhost:3121/xilinx_tcf/Digilent/210276AC80A2. Trying next device.
INFO: [Labtoolstcl 44-464] Closing hw_target localhost:3121/xilinx_tcf/Digilent/210276AC80A2
INFO: Trying to use hardware target localhost:3121/xilinx_tcf/Digilent/210276AC80A2B
INFO: [Labtoolstcl 44-466] Opening hw_target localhost:3121/xilinx_tcf/Digilent/210276AC80A2B
INFO: Opened hardware target localhost:3121/xilinx_tcf/Digilent/210276AC80A2B on try 1.
INFO: Found xc7a200tsbg484-1 as part of xc7a200t_0.
INFO: Programming bitstream to device xc7a200t_0 on target localhost:3121/xilinx_tcf/Digilent/210276AC80A2B.
INFO: [Labtools 27-3164] End of startup status: HIGH
program_hw_devices: Time (s): cpu = 00:00:06 ; elapsed = 00:00:06 . Memory (MB): peak = 1386.867 ; gain = 0.000 ; free physical = 7045 ; free virtual = 24260
INFO: [Labtoolstcl 44-464] Closing hw_target localhost:3121/xilinx_tcf/Digilent/210276AC80A2B

INFO: SUCCESS! FPGA xc7a200tsbg484-1 successfully programmed with bitstream lowrisc_systems_top_earlgrey_nexysvideo_0.1.bit.
```
If that worked you should see some text from the UART which looks like:
```
I00000 boot_rom.c:35] Version:    opentitan-snapshot-20191101-1-1130-g783edaf44
Build Date: 2021-02-09, 12:46:54
```
Now build the AES test and run it on the FPGA:
```
$ build-bin/sw/host/spiflash/spiflash --input build-bin/sw/device/tests/aes_test_fpga_nexysvideo.bin
Running SPI flash update.
Image divided into 8 frames.
frame: 0x00000000 to offset: 0x00000000
frame: 0x00000001 to offset: 0x000003d8
frame: 0x00000002 to offset: 0x000007b0
frame: 0x00000003 to offset: 0x00000b88
frame: 0x00000004 to offset: 0x00000f60
frame: 0x00000005 to offset: 0x00001338
frame: 0x00000006 to offset: 0x00001710
frame: 0x80000007 to offset: 0x00001ae8
```
The UART output shows the result of running the test:
```
I00000 boot_rom.c:35] Version:    opentitan-snapshot-20191101-1-1130-g783edaf44
Build Date: 2021-02-09, 12:46:54

I00001 bootstrap.c:138] Bootstrap requested, initialising HW...
I00002 bootstrap.c:142] HW initialisation completed, waiting for SPI input...
I00009 bootstrap.c:92] Processing frame #0, expecting #3
I00010 bootstrap.c:92] Processing frame #3, expecting #3
I00011 bootstrap.c:92] Processing frame #0, expecting #4
I00012 bootstrap.c:92] Processing frame #4, expecting #4
I00018 bootstrap.c:92] Processing frame #7, expecting #7
I00019 bootstrap.c:122] Bootstrap: DONE!
I00020 boot_rom.c:44] Boot ROM initialisation has completed, jump into flash!
I65535 aes_test.c:35] Running AES test
I00000 test_status.c:26] PASS!
```

### Testing with the Silver Oak version of the AES Core
Follow the steps above to copy over the Silver Oak generated AES hardware design:
```console
$ cd silveroak/silveroak-opentitan/aes
$ ./copy_to_opentitan.sh
```

Regenerate the FPGA design using the Silver Oak AES core:
```console
$ fusesoc --cores-root . run --target=synth lowrisc:systems:top_earlgrey_nexysvideo
```

Run the `aes_test.c` program.
```console
$ build-bin/sw/host/spiflash/spiflash --input build-bin/sw/device/tests/aes_test_fpga_nexysvideo.bin
```

The UART output reports the test status.
```
I00000 boot_rom.c:35] Version:    opentitan-snapshot-20191101-1-1130-g783edaf44
Build Date: 2021-02-09, 12:46:54

I00001 bootstrap.c:138] Bootstrap requested, initialising HW...
I00002 bootstrap.c:142] HW initialisation completed, waiting for SPI input...
I00018 bootstrap.c:92] Processing frame #7, expecting #7
I00019 bootstrap.c:122] Bootstrap: DONE!
I00020 boot_rom.c:44] Boot ROM initialisation has completed, jump into flash!
I65535 aes_test.c:35] Running AES test
I00000 test_status.c:26] PASS!
```
