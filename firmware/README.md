# Formal Verification of OpenTitan Firmware with Bedrock2

## Intro

The Silver Oak project has the goal of creating fully verified systems that involve both hardware and software. Silver Oak is implemented in the Coq proof assistant, with [bedrock2](https://github.com/mit-plv/bedrock2), which is an experimental framework that allows us to transcribe C code in Coq.
As a part of the project, this is an experimental project to formally verify firmware in [OpenTitan](https://github.com/lowRISC/opentitan), which consists of simple hardware devices and driver firmware. The drivers are written in C and uses memory-mapped I/O (MMIO) registers to interact with a hardware device.
The goal of this sub-project is to transcribe selected firmware source with bedrock2, write a formal specification in Coq, and verify the MMIO-based software-hardware interface.

## Setup

First, setup OpenTitan and SilverOak repositories and build them:

**OpenTitan**

Follow the [Getting started with Verilator](https://docs.opentitan.org/doc/ug/getting_started_verilator/) to setup test environment for OpenTitan with Verilator.
You may need to install prerequisites and software tools before starting the simulation with Verilator.

**SilverOak**

Follow the [SilverOak README](https://github.com/project-oak/silveroak) to setup the silveroak repository.

**Important Directories:**

> :warning: All the firmware except for AES is based on the latest OpenTitan `master` branch instead of the tagged submodule.

* `opentitan/sw/device/silicon_creator/lib/drivers`: main sources to transcribe
* `silveroak/third_party/bedrock2`: tagged bedrock2 submodule
* `silveroak/firmware`: bedrock2 sources (this project)

Following table summarizes the status of each driver.

(:heavy_check_mark:: Done, :construction:: Work-in-Progress)

| Directory | Firmware Sources | Transcription | Semantics | Properties |
|:-----|:----|:--:|:--:|:--:|
| LibBase | bitfield.h <br> abs_mmio.h <br> sec_mmio.h | :heavy_check_mark: <br> :heavy_check_mark: <br> :construction: | N/A <br> N/A <br> N/A | :heavy_check_mark: <br> :heavy_check_mark: <br> :construction: |
| Uart | uart.c | :heavy_check_mark: | :heavy_check_mark: | :construction: |
| Hmac | hmac.c | :heavy_check_mark: | :heavy_check_mark: | :construction: |
| Keymgr | keymgr.c | :heavy_check_mark: | | |
| Otp | otp.c | :construction: | | |
| Rstmgr | rstmgr.c ||||
| Alert| alert.c ||||

Note that the following directories contain initial experiments. These won't be included in the OpenTitan's silicon creator mask ROM.

| Direcotry | Firware Source |
| :------|:---|
| Aes | opentitan/sw/device/lib/dif/dif_aes.c |
| IncrementWait | N/A |

## Transcribing C code

To understand Bedrock2 syntax, it is recommended to look directly at [the file where they define it](https://github.com/mit-plv/bedrock2/blob/master/bedrock2/src/bedrock2/NotationsCustomEntry.v)
It's some advanced use of Coq's Notation construct, but you can kind of search for what you want to do and figure out what the syntax might be.

You can also figure out what operations are available by running `Print Syntax.cmd.cmd` and `Print Syntax.expr.expr`. A function in bedrock2 is the function name, argument names, return value names, and the function body, which is a `Syntax.cmd.cmd` type. Some of the `cmd` constructors take `expr` as an argument -- `Syntax.expr.expr` will show you those. Finally, one of the expr constructors constructs a binary operation; `Print Syntax.bopname.bopname` shows you the options for that.

The source file is [here](https://github.com/mit-plv/bedrock2/blob/master/bedrock2/src/bedrock2/Syntax.v), if you want to look at them all at once.


If it's easier to start with, you can skip bedrock_func_body:( (which opens the bedrock2 notation scope) and just write the function body directly in bedrock2. It would look something like cmd.seq (cmd.set "x" (expr.literal 1)) (cmd.set "x" (expr. op bopname.add (expr.var "x") (expr.literal 1))) for x = 1; x += 1. Pretty verbose, but writing the expressions directly might help you in figuring out what you want to say before you write it in the notation.


### Structs

As for structs in bedrock2, it's not currently supported.

We currently handle this by passing the fields separately and making a wrapper function in the C file that extracted the fields and called the bedrock2-generated function. See the [Bitfield](https://github.com/project-oak/silveroak/blob/0fb12e149f8af0c7bb71f9d428a5ef481e6dabdc/investigations/bedrock2/LibBase/Bitfield.v#L39) example.


### Testing

To run the unit tests, run following command in the OpenTitan's root directory, where `<silveroak>` is the SilverOak repo top and `<device>` is the device source file name without `.c` extension.
For example, to test `uart.c`, replace `<device>` with `uart`.

```
# in opentitan repo top
<silveroak>/investigations/bedrock2/run_silicon_creator_tests_in_opentitan.sh <device>
```

This will automatically replace the corresponding firmware source file with the transcribed one by Bedrock2, and then run unit tests.
For `uart` and `hmac`, functional tests will also run.


## Bedrock2 Suggestions

### Operators

Missing operators that might be very helpful if added:
* Logical operators (`||`,`&&`,`!`)
* Unary binary operators (`~`)

### Proofs

* here are a lot of bitfield operations in the firmware. Sam mentioned that there will be some updates in bedrock2 that makes bit operations much easier to handle.
