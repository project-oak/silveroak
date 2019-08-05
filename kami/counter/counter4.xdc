#
# Copyright 2019 The Project Oak Authors
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

create_clock -period 8.000 -name CLK_125_P -waveform {0.000 4.000} -add [get_ports CLK_125_P]
set_property PACKAGE_PIN F23 [get_ports CLK_125_P]
set_property IOSTANDARD LVDS [get_ports CLK_125_P]


set_property IOSTANDARD LVCMOS33 [get_ports GPIO_PB_SW3]
set_property PACKAGE_PIN C3 [get_ports GPIO_PB_SW3]

