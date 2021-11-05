### Running OpenTitan SHA256 in Simulation

First, set up your system as described in https://docs.opentitan.org/doc/ug/install_instructions/.
On Fedora 34, the required system packages can be installed using

```
sudo dnf install autoconf bison @development-tools clang-tools-extra cmake curl \
    doxygen flex g++ git golang elfutils-libelf elfutils-libelf-devel \
    libftdi libftdi-devel libusbx redhat-lsb make ncurses ninja-build \
    openssl-libs openssl-devel perl pkgconf python3 python3-pip \
    python3-setuptools python3-wheel srecord tree libxslt zlib-devel xz
```

Then, run the following setup commands inside `third_party/opentitan`:

```
pip3 install --user -r python-requirements.txt # they changed, so it's not sufficient to have run this in the outdated opentitan submodule of silveroak
./meson_init.sh
fusesoc --cores-root . run --flag=fileset_top --target=sim --setup --build lowrisc:dv:chip_verilator_sim
```

And compile the OpenTitan software:

```
ninja -C build-out all
```

Then, to run the unmodified OpenTitan SHA256 functional test simulation:

```
build/lowrisc_dv_chip_verilator_sim_0.1/sim-verilator/Vchip_sim_tb \
    --meminit=rom,build-out/sw/device/boot_rom/boot_rom_sim_verilator.scr.39.vmem \
    --meminit=otp,build-out/sw/device/otp_img/otp_img_sim_verilator.vmem \
    --meminit=flash,build-out/sw/device/silicon_creator/testing/sw_silicon_creator_lib_driver_hmac_functest_sim_verilator.elf
```

### Replacing the OpenTitan SHA256 driver by the bedrock2 SHA256 driver

First, compile all Coq sources by running `make` in the toplevel silveroak directory.

Then, in `silveroak/silveroak-opentitan/hmac/sw/`, run

```
make b2_sha256.a
```

to produce the Coq-generated RISC-V instructions (`b2_sha256.hex`) and transform them into an object file `b2_sha256.o`, which you can inspect using

```
/tools/riscv/bin/riscv32-unknown-elf-objdump -Dt b2_sha256.o
```

Note: the above `make` command actually produces an archive file (`.a`) containing just one single `.o` file, because the meson build system only looks for `.a` files.

Then, in `silveroak/third_party/opentitan/sw/device/silicon_creator/lib/drivers/meson.build`, replace the definition

```
# Mask ROM hmac driver
sw_silicon_creator_lib_driver_hmac = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_driver_hmac',
    sources: [
      hw_ip_hmac_reg_h,
      'hmac.c',
    ],
    dependencies: [
      sw_silicon_creator_lib_base_abs_mmio,
    ],
  ),
)
```

by

```
c = meson.get_compiler('c')
libdir = meson.current_source_dir() + '/../../../../../../../silveroak-opentitan/hmac/sw/'
message(libdir)
precompiled_dep = c.find_library('b2_sha256', dirs : [libdir])
sw_silicon_creator_lib_driver_hmac = declare_dependency(
  link_with: static_library(
    'sw_silicon_creator_lib_driver_hmac',
    sources: [
      libdir + 'b2_sha256.h'
    ],
    dependencies: [
      precompiled_dep
    ],
  ),
)
```

and in `silveroak/third_party/opentitan/sw/device/silicon_creator/lib/drivers/hmac_functest.c`, in function `hmac_test`, replace

```
  hmac_sha256_init();
  RETURN_IF_ERROR(
      hmac_sha256_update(kGettysburgPrelude, sizeof(kGettysburgPrelude) - 1));

  hmac_digest_t digest;
  RETURN_IF_ERROR(hmac_sha256_final(&digest));
```

by

```
  hmac_digest_t digest;
  b2_sha256(&digest, kGettysburgPrelude, sizeof(kGettysburgPrelude) - 1);
```

and at the top of that file, after the `#include`s, add

```
#include "../../silveroak-opentitan/hmac/sw/b2_sha256.h"
```

and then in `silveroak/third_party/opentitan`, run

```
./meson_init.sh -r
```

to reconfigure the build directories to reflect that change, and rebuild just the SHA256 functest:

```
ninja -C build-out sw/device/silicon_creator/testing/sw_silicon_creator_lib_driver_hmac_functest_sim_verilator.elf
```

And now that the elf file contains the bedrock2 driver instead of the OpenTitan driver, run the Verilator simulation again:

```
build/lowrisc_dv_chip_verilator_sim_0.1/sim-verilator/Vchip_sim_tb \
    --meminit=rom,build-out/sw/device/boot_rom/boot_rom_sim_verilator.scr.39.vmem \
    --meminit=otp,build-out/sw/device/otp_img/otp_img_sim_verilator.vmem \
    --meminit=flash,build-out/sw/device/silicon_creator/testing/sw_silicon_creator_lib_driver_hmac_functest_sim_verilator.elf
```

It should still say that the test passed.

But now, let's also check that we're testing the right thing, i.e. let's deliberately break the test:

For instance, in `silveroak/silveroak-opentitan/hmac/sw/Hmac.v`, in the last function, replace

```
       while (i < 8) {
```

by

```
       while (i < 7) {
```

and in `silveroak/silveroak-opentitan/hmac/sw`, run `make` again.
This will break a proof in `HmacProperties.v`
At the line where it breaks, write `Admitted.`, and comment out (using `(*` and `*)`) the rest of the proof (but leave the `End Proofs.` in place).
Then, run `make` in `silveroak/silveroak-opentitan/hmac/sw` again, and also run `make b2_sha256.a` again.

Optionally, it can be interesting to use a diff tool to see that the `objdump` output changed in exactly one line.

Then, in `silveroak/third_party/opentitan/sw/device/silicon_creator/lib/drivers/hmac_functest.c`, add some spaces at the end of a line and save it again, to make sure ninja will not assume that there were no changes (it doesn't seem to track changes to external libraries like `b2_sha256.a`).

Then, in `silveroak/third_party/opentitan`, run the ninja and verilator commands again:

```
ninja -C build-out sw/device/silicon_creator/testing/sw_silicon_creator_lib_driver_hmac_functest_sim_verilator.elf
```

```
build/lowrisc_dv_chip_verilator_sim_0.1/sim-verilator/Vchip_sim_tb \
    --meminit=rom,build-out/sw/device/boot_rom/boot_rom_sim_verilator.scr.39.vmem \
    --meminit=otp,build-out/sw/device/otp_img/otp_img_sim_verilator.vmem \
    --meminit=flash,build-out/sw/device/silicon_creator/testing/sw_silicon_creator_lib_driver_hmac_functest_sim_verilator.elf
```

Now it should say that the tests failed.


### Notes

* It seems that files are first compiled and placed into `build-out`, and then copied to `build-bin`, but if the copying doesn't take place, `build-bin` still contains outdated files, so we use `build-bin` everywhere above just to be safe.
* These instructions were tested using OpenTitan as a git submodule at `third_party/opentitan`, at commit `ddcfe93f1f669f192ff4a33f1c19d827663a921f` (Oct 26, 2021).
* `LOG_INFO` calls in `hmac_functest.c` are logged in `opentitan/uart0.log`. Changing the string passed to `LOG_INFO`, running the simulation again, and checking `uart0.log` can help you convince yourself that the most recent version was run.
