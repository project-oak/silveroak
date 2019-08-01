set_property PACKAGE_PIN D5 [get_ports {GPIO_LED[0]}]
set_property IOSTANDARD LVCMOS33 [get_ports {GPIO_LED[0]}]
set_property IOSTANDARD LVCMOS33 [get_ports {GPIO_LED[1]}]
set_property IOSTANDARD LVCMOS33 [get_ports {GPIO_LED[2]}]
set_property IOSTANDARD LVCMOS33 [get_ports {GPIO_LED[3]}]
set_property PACKAGE_PIN D6 [get_ports {GPIO_LED[1]}]
set_property PACKAGE_PIN A5 [get_ports {GPIO_LED[2]}]
set_property PACKAGE_PIN B4 [get_ports GPIO_PB_SW0]
set_property IOSTANDARD LVCMOS33 [get_ports GPIO_PB_SW0]
set_property PACKAGE_PIN B5 [get_ports {GPIO_LED[3]}]

create_clock -period 8.000 -name CLK_125_P -waveform {0.000 4.000} [get_ports CLK_125_P]
set_property PACKAGE_PIN F23 [get_ports CLK_125_P]
set_property IOSTANDARD LVDS [get_ports CLK_125_P]


set_property IOSTANDARD LVCMOS33 [get_ports GPIO_PB_SW3]
set_property PACKAGE_PIN C3 [get_ports GPIO_PB_SW3]
