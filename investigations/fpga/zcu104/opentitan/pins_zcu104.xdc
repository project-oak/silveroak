## Clock Signal using differential 125MHz input
create_clock -period 8.000 -name CLK_125_P -waveform {0.000 4.000} -add [get_ports CLK_125_P]
set_property PACKAGE_PIN F23 [get_ports CLK_125_P]
set_property IOSTANDARD LVDS [get_ports CLK_125_P]

create_generated_clock -name clk_50_unbuf -source [get_pin clkgen/pll/CLKIN1] [get_pin clkgen/pll/CLKOUT0]
create_generated_clock -name clk_48_unbuf -source [get_pin clkgen/pll/CLKIN1] [get_pin clkgen/pll/CLKOUT1]
set_clock_groups -group clk_50_unbuf -group clk_48_unbuf -asynchronous
set_property CONFIG_VOLTAGE 3.3 [current_design]
set_property CFGBVS VCCO [current_design]


# Reset with SW18
set_property -dict { PACKAGE_PIN C3 IOSTANDARD LVCMOS33 } [get_ports { IO_RST }];

## UART
set_property -dict { PACKAGE_PIN A20 IOSTANDARD LVCMOS18 } [get_ports { IO_URX }];
set_property -dict { PACKAGE_PIN C19 IOSTANDARD LVCMOS18 } [get_ports { IO_UTX }];

set_property SEVERITY {Warning} [get_drc_checks UCIO-1]
set_property SEVERITY {Warning} [get_drc_checks NSTD-1]


