--
-- Copyright 2019 The Project Oak Authors
--
-- Licensed under the Apache License, Version 2.0 (the "License");
-- you may not use this file except in compliance with the License.
-- You may obtain a copy of the License at
--
--     http://www.apache.org/licenses/LICENSE-2.0
--
-- Unless required by applicable law or agreed to in writing, software
-- distributed under the License is distributed on an "AS IS" BASIS,
-- WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-- See the License for the specific language governing permissions and
-- limitations under the License.
--

-- A simple test program for the Xilinx ZCU104605 development board that
-- makes the user GPIO LEDs flash for the binary sequence 0..7, with a
-- reset from the push button GPIO_PB_SW3 SW18 at a 1 second frequency.

package counter_package is
  subtype count_type is natural range 0 to 15;
end package counter_package;

library ieee;
use ieee.std_logic_1164.all;
use work.counter_package.all;
entity leds is
  port (signal CLK_125_P   : in std_ulogic; -- 125MHz clock P at pin H11 LVDS
        signal CLK_125_N   : in std_ulogic; -- 125MHz clock N at pin G11 LVDS
        signal GPIO_PB_SW3 : in std_ulogic; -- pin C3 LVCMOS33 connected to push-button GPIO_PB_SW3 SW18 
        signal GPIO_LED    : out count_type -- LEDs at pins D5 (LSB), D6, A5, B5 (MSB) LVCMOS33
       );
end entity leds;

library unisim;
use unisim.vcomponents.all;
architecture behavioral of leds is
  signal count : count_type := 0 ;
  signal clk : std_ulogic;
begin

  clock_buffer : ibufgds port map (o => clk, i => CLK_125_P, ib => CLK_125_N);

  clock_divider : process is
    variable divider_count : natural := 0;
  begin
    wait until clk'event and clk = '1';
    if GPIO_PB_SW3 = '1' then
      count <= 0;
      divider_count := 0;
    else
      if divider_count = 125000000 then
       divider_count := 0;
        count <= (count + 1) mod 16;
      else
        divider_count := divider_count + 1;
      end if;
    end if;
  end process clock_divider;

  GPIO_LED <= count;

end architecture behavioral;

