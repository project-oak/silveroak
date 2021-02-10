# AES Silver Oak Implementation

## Baseline OpenTitan version for comparison
We must use the snapshot of the OpenTitan source from 11 May 2020 as the baseline reference implementation
at commit hash [783edaf444](https://github.com/lowRISC/opentitan/tree/783edaf444eb0d9eaf9df71c785089bffcda574e) on the OpenTitan GitHub repo. For consistency and to allow us to produce a single FPGA implementation we should design and verify all our Silver Oak OpenTitan
components against this OpenTitan commit hash.

## Generating utilization reports
To generate utilization reports for all the circuit modules type:
```console
$ make util
```
To generate a utilization report for a particular module invoke the Makefile with the name of the module followed by `_util` e.g.
```console
$ make aes_sub_bytes_util
```
This will generate an FPGA implementation sub-directory in the directrory `aes_implemention`:
```console
$ ls aes_implemention
aes_sub_bytes
```
There might be other circuit implenetations thre from previous runs.
Two reports are of itnerest:
* The post synthesis utilization report which gives an approximate resource utilization.
* The post-placement and optimization which gives an accurate utilization report.

For the `aes_sub_bytes` component these reports can be found in the `aes_implementation` subdirectory after implementation at:
* Post synthesis: `aes_implementation/aes_sub_bytes/post_synth_util.rpt`
* Post place and route: `aes_implementation/aes_sub_bytes/post_route_util.rpt`

## Baseline OpenTitan SystemVerilog Components
* [aes_mix_columns.sv](https://github.com/lowRISC/opentitan/blob/783edaf444eb0d9eaf9df71c785089bffcda574e/hw/ip/aes/rtl/aes_mix_columns.sv)
* [aes_sub_bytes.sv](https://github.com/lowRISC/opentitan/blob/783edaf444eb0d9eaf9df71c785089bffcda574e/hw/ip/aes/rtl/aes_sub_bytes.sv)
* [aes_shift_rows.sv](https://github.com/lowRISC/opentitan/blob/783edaf444eb0d9eaf9df71c785089bffcda574e/hw/ip/aes/rtl/aes_shift_rows.sv)
* [aes_sbox.sv](https://github.com/lowRISC/opentitan/blob/783edaf444eb0d9eaf9df71c785089bffcda574e/hw/ip/aes/rtl/aes_sbox.sv)

## Mix Columns Performance Comparison
### OpenTitan `aes_mix_columns` baseline block
We have synthesized and implemented the OpenTitan `aes_mix_columns` in isolation to produce the following utilization report from Vivado. The synthesis report shows the design uses 259 LUTs.
```
-----------------------------------------------------------------------------------
| Tool Version : Vivado v.2018.3 (lin64) Build 2405991 Thu Dec  6 23:36:41 MST 2018
| Date         : Fri Jan 29 00:20:16 2021
| Host         : glasgow.mtv.corp.google.com running 64-bit Debian GNU/Linux rodete
| Command      : report_utilization -file aes_mix_columns_utilization_synth.rpt -pb aes_mix_columns_utilization_synth.pb
| Design       : aes_mix_columns
| Device       : 7a200tsbg484-1
| Design State : Synthesized
-----------------------------------------------------------------------------------

+-------------------------+------+-------+-----------+-------+
|        Site Type        | Used | Fixed | Available | Util% |
+-------------------------+------+-------+-----------+-------+
| Slice LUTs*             |  259 |     0 |    134600 |  0.19 |
|   LUT as Logic          |  259 |     0 |    134600 |  0.19 |
```

After implementation the utilization is reduced to 253 LUTs:

```
+-------------------------+------+-------+-----------+-------+
|        Site Type        | Used | Fixed | Available | Util% |
+-------------------------+------+-------+-----------+-------+
| Slice LUTs              |  253 |     0 |    133800 |  0.19 |
|   LUT as Logic          |  253 |     0 |    133800 |  0.19 |

+------------------------------------------+------+-------+-----------+-------+
|                 Site Type                | Used | Fixed | Available | Util% |
+------------------------------------------+------+-------+-----------+-------+
| Slice                                    |   75 |     0 |     33450 |  0.22 |
|   SLICEL                                 |   55 |     0 |           |       |
|   SLICEM                                 |   20 |     0 |           |       |
| LUT as Logic                             |  253 |     0 |    133800 |  0.19 |
|   using O5 output only                   |    0 |       |           |       |
|   using O6 output only                   |  190 |       |           |       |
|   using O5 and O6                        |   63 |       |           |       |
| LUT as Memory                            |    0 |     0 |     46200 |  0.00 |
|   LUT as Distributed RAM                 |    0 |     0 |           |       |
|   LUT as Shift Register                  |    0 |     0 |           |       |
| Slice Registers                          |    0 |     0 |    267600 |  0.00 |
|   Register driven from within the Slice  |    0 |       |           |       |
|   Register driven from outside the Slice |    0 |       |           |       |
| Unique Control Sets                      |    0 |       |     33450 |  0.00 |
+------------------------------------------+------+-------+-----------+-------+

```

### Silver Oak `aes_mix_columns` block
After synthesis the Silver Oak AES block turns out to use 184 LUTs.
```
-----------------------------------------------------------------------------------
| Tool Version : Vivado v.2018.3 (lin64) Build 2405991 Thu Dec  6 23:36:41 MST 2018
| Date         : Wed Feb  3 10:08:57 2021
| Host         : satnam-glaptop running 64-bit Debian GNU/Linux rodete
| Command      : report_utilization -file ./aes_implementation/aes_mix_columns/post_synth_util.rpt
| Design       : aes_mix_columns
| Device       : 7a200tsbg484-1
| Design State : Synthesized
-----------------------------------------------------------------------------------

+-------------------------+------+-------+-----------+-------+
|        Site Type        | Used | Fixed | Available | Util% |
+-------------------------+------+-------+-----------+-------+
| Slice LUTs*             |  264 |     0 |    134600 |  0.20 |
|   LUT as Logic          |  264 |     0 |    134600 |  0.20 |
|   LUT as Memory         |    0 |     0 |     46200 |  0.00 |

```
After placement and optmization:
```
+-------------------------+------+-------+-----------+-------+
|        Site Type        | Used | Fixed | Available | Util% |
+-------------------------+------+-------+-----------+-------+
| Slice LUTs              |  262 |     0 |    133800 |  0.20 |
|   LUT as Logic          |  262 |     0 |    133800 |  0.20 |


+------------------------------------------+------+-------+-----------+-------+
|                 Site Type                | Used | Fixed | Available | Util% |
+------------------------------------------+------+-------+-----------+-------+
| Slice                                    |   75 |     0 |     33450 |  0.22 |
|   SLICEL                                 |   57 |     0 |           |       |
|   SLICEM                                 |   18 |     0 |           |       |
| LUT as Logic                             |  262 |     0 |    133800 |  0.20 |
|   using O5 output only                   |    0 |       |           |       |
|   using O6 output only                   |  204 |       |           |       |
|   using O5 and O6                        |   58 |       |           |       |
| LUT as Memory                            |    0 |     0 |     46200 |  0.00 |
|   LUT as Distributed RAM                 |    0 |     0 |           |       |
|   LUT as Shift Register                  |    0 |     0 |           |       |
| Slice Registers                          |    0 |     0 |    267600 |  0.00 |
|   Register driven from within the Slice  |    0 |       |           |       |
|   Register driven from outside the Slice |    0 |       |           |       |
| Unique Control Sets                      |    0 |       |     33450 |  0.00 |
+------------------------------------------+------+-------+-----------+-------+


```
The current Silver Oak `aes_mix_columns` has 4% greater utilization than the
OpenTitan version.

A picture of the `aes_mix_columns` schematic in Vivado:

![ot_mixcols](ot_mix_cols.png)


## SubBytes Performance Comparison
A comparison of the OpenTitan `aes_sub_bytes` module and the Silver Oak
version shows identitcal LUT utilization.
### OpenTitan `aes_sub_bytes` baseline block
OpenTitan version synthesis report:
```
+-------------------------+------+-------+-----------+-------+
|        Site Type        | Used | Fixed | Available | Util% |
+-------------------------+------+-------+-----------+-------+
| Slice LUTs*             | 1152 |     0 |    134600 |  0.86 |
|   LUT as Logic          | 1152 |     0 |    134600 |  0.86 |
|   LUT as Memory         |    0 |     0 |     46200 |  0.00 |
| Slice Registers         |    0 |     0 |    269200 |  0.00 |
|   Register as Flip Flop |    0 |     0 |    269200 |  0.00 |
|   Register as Latch     |    0 |     0 |    269200 |  0.00 |
| F7 Muxes                |  512 |     0 |     67300 |  0.76 |
| F8 Muxes                |    0 |     0 |     33650 |  0.00 |
+-------------------------+------+-------+-----------+-------+
```
OpenTitan version utilization after implementation and optmization:
```
+------------------------------------------+------+-------+-----------+-------+
|                 Site Type                | Used | Fixed | Available | Util% |
+------------------------------------------+------+-------+-----------+-------+
| Slice                                    |  337 |     0 |     33450 |  1.01 |
|   SLICEL                                 |  234 |     0 |           |       |
|   SLICEM                                 |  103 |     0 |           |       |
| LUT as Logic                             | 1152 |     0 |    133800 |  0.86 |
|   using O5 output only                   |    0 |       |           |       |
|   using O6 output only                   | 1152 |       |           |       |
|   using O5 and O6                        |    0 |       |           |       |
| LUT as Memory                            |    0 |     0 |     46200 |  0.00 |
|   LUT as Distributed RAM                 |    0 |     0 |           |       |
|   LUT as Shift Register                  |    0 |     0 |           |       |
| Slice Registers                          |    0 |     0 |    267600 |  0.00 |
|   Register driven from within the Slice  |    0 |       |           |       |
|   Register driven from outside the Slice |    0 |       |           |       |
| Unique Control Sets                      |    0 |       |     33450 |  0.00 |
+------------------------------------------+------+-------+-----------+-------+
```
### Silver Oak `aes_sub_bytes` baseline block
Silver Oak version after synthesis:
```
+-------------------------+------+-------+-----------+-------+
|        Site Type        | Used | Fixed | Available | Util% |
+-------------------------+------+-------+-----------+-------+
| Slice LUTs*             | 1152 |     0 |    134600 |  0.86 |
|   LUT as Logic          | 1152 |     0 |    134600 |  0.86 |
|   LUT as Memory         |    0 |     0 |     46200 |  0.00 |
| Slice Registers         |    0 |     0 |    269200 |  0.00 |
|   Register as Flip Flop |    0 |     0 |    269200 |  0.00 |
|   Register as Latch     |    0 |     0 |    269200 |  0.00 |
| F7 Muxes                |  512 |     0 |     67300 |  0.76 |
| F8 Muxes                |    0 |     0 |     33650 |  0.00 |
+-------------------------+------+-------+-----------+-------+
```
Silver Oak version after routing:
```
+------------------------------------------+------+-------+-----------+-------+
|                 Site Type                | Used | Fixed | Available | Util% |
+------------------------------------------+------+-------+-----------+-------+
| Slice                                    |  338 |     0 |     33450 |  1.01 |
|   SLICEL                                 |  239 |     0 |           |       |
|   SLICEM                                 |   99 |     0 |           |       |
| LUT as Logic                             | 1152 |     0 |    133800 |  0.86 |
|   using O5 output only                   |    0 |       |           |       |
|   using O6 output only                   | 1152 |       |           |       |
|   using O5 and O6                        |    0 |       |           |       |
| LUT as Memory                            |    0 |     0 |     46200 |  0.00 |
|   LUT as Distributed RAM                 |    0 |     0 |           |       |
|   LUT as Shift Register                  |    0 |     0 |           |       |
| Slice Registers                          |    0 |     0 |    267600 |  0.00 |
|   Register driven from within the Slice  |    0 |       |           |       |
|   Register driven from outside the Slice |    0 |       |           |       |
| Unique Control Sets                      |    0 |       |     33450 |  0.00 |
+------------------------------------------+------+-------+-----------+-------+

```

## SBox LUT Performance Comparison
### OpenTitan `aes_sbox_lut` baseline block
After synthesis the utilization for the OpenTitan `aes_sbox_lut` baseline block is:
```
+-------------------------+------+-------+-----------+-------+
|        Site Type        | Used | Fixed | Available | Util% |
+-------------------------+------+-------+-----------+-------+
| Slice LUTs*             |   72 |     0 |    134600 |  0.05 |
|   LUT as Logic          |   72 |     0 |    134600 |  0.05 |
|   LUT as Memory         |    0 |     0 |     46200 |  0.00 |

```
After implementation:
```
+------------------------------------------+------+-------+-----------+-------+
|                 Site Type                | Used | Fixed | Available | Util% |
+------------------------------------------+------+-------+-----------+-------+
| Slice                                    |   22 |     0 |     33450 |  0.07 |
|   SLICEL                                 |   17 |     0 |           |       |
|   SLICEM                                 |    5 |     0 |           |       |
| LUT as Logic                             |   72 |     0 |    133800 |  0.05 |
|   using O5 output only                   |    0 |       |           |       |
|   using O6 output only                   |   72 |       |           |       |
|   using O5 and O6                        |    0 |       |           |       |
| LUT as Memory                            |    0 |     0 |     46200 |  0.00 |
|   LUT as Distributed RAM                 |    0 |     0 |           |       |
|   LUT as Shift Register                  |    0 |     0 |           |       |
| Slice Registers                          |    0 |     0 |    267600 |  0.00 |
|   Register driven from within the Slice  |    0 |       |           |       |
|   Register driven from outside the Slice |    0 |       |           |       |
| Unique Control Sets                      |    0 |       |     33450 |  0.00 |
+------------------------------------------+------+-------+-----------+-------+
```

### Silver Oak `aes_sbox_lut` block
After synthesis:
```
+-------------------------+------+-------+-----------+-------+
|        Site Type        | Used | Fixed | Available | Util% |
+-------------------------+------+-------+-----------+-------+
| Slice LUTs*             |   72 |     0 |    134600 |  0.05 |
|   LUT as Logic          |   72 |     0 |    134600 |  0.05 |
```
After implementation:
```
+------------------------------------------+------+-------+-----------+-------+
|                 Site Type                | Used | Fixed | Available | Util% |
+------------------------------------------+------+-------+-----------+-------+
| Slice                                    |   22 |     0 |     33450 |  0.07 |
|   SLICEL                                 |   16 |     0 |           |       |
|   SLICEM                                 |    6 |     0 |           |       |
| LUT as Logic                             |   72 |     0 |    133800 |  0.05 |
|   using O5 output only                   |    0 |       |           |       |
|   using O6 output only                   |   72 |       |           |       |
|   using O5 and O6                        |    0 |       |           |       |
| LUT as Memory                            |    0 |     0 |     46200 |  0.00 |
|   LUT as Distributed RAM                 |    0 |     0 |           |       |
|   LUT as Shift Register                  |    0 |     0 |           |       |
| Slice Registers                          |    0 |     0 |    267600 |  0.00 |
|   Register driven from within the Slice  |    0 |       |           |       |
|   Register driven from outside the Slice |    0 |       |           |       |
| Unique Control Sets                      |    0 |       |     33450 |  0.00 |
+------------------------------------------+------+-------+-----------+-------+
```
The Silver Oak block has identical utilization.

