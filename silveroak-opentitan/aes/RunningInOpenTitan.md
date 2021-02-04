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

# Replace the combinational components

1. Make sure the SilverOak AES components were built by the first step.
1. Then whilst in the `silveroak-opentitan/aes` directory run `./copy_to_opentitan.sh`
1. The SilverOak components should now be in `third_party/opentitan/hw/ip/aes/rtl/`

# Build the OpenTitan Verilator model

1. Navigate to third_party/opentitan, and run fusesoc:

```
fusesoc --cores-root . run --flag=fileset_top --target=sim --setup --build lowrisc:systems:top_earlgrey_verilator
```

# Run the aes_test.c

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
