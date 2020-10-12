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

library ieee;
use ieee.std_logic_1164.all;
package counter_package is
  subtype count_type is natural range 0 to 15;
  
  component mkModule1 is
    port(signal CLK : in std_ulogic;
         signal RST_N : in std_ulogic;
         signal EN_count_value : in std_ulogic;
         signal count_value : out count_type;
         signal RDY_count_value : out std_ulogic);
  end component mkModule1;
  
end package counter_package;


library ieee;
use ieee.std_logic_1164.all;
use work.counter_package.all;
entity counter4 is
  port (signal CLK_125_P   : in std_ulogic; -- 125MHz clock P at pin H11 LVDS
        signal CLK_125_N   : in std_ulogic; -- 125MHz clock N at pin G11 LVDS
        signal GPIO_PB_SW3 : in std_ulogic; -- pin C3 LVCMOS33 connected to push-button GPIO_PB_SW3 SW18 
        signal GPIO_LED    : out count_type -- LEDs at pins D5 (LSB), D6, A5, B5 (MSB) LVCMOS33
       );
end entity counter4;

library unisim;
use unisim.vcomponents.all;
architecture behavioral of counter4 is
  signal count : count_type;
  signal clk125MHz, clk1Hz : std_ulogic := '0';
  signal inv_rest : std_ulogic;
  signal en : std_ulogic := '1';
  signal inv_reset : std_ulogic;
begin

  clock_buffer : ibufgds port map (o => clk125MHz, i => CLK_125_P, ib => CLK_125_N);

  clock_divider : process is
    variable divider_count : natural := 0;
  begin
    wait until clk125MHz'event and clk125MHz = '1';
    if divider_count = 62500000 then
     clk1Hz <= not clk1Hz;
     divider_count := 0;
    else
      divider_count := divider_count + 1;
    end if;
  end process clock_divider;

  inv_reset <= not GPIO_PB_SW3;

  kami_counter : mkModule1 port map (CLK => clk1Hz,
                                     RST_N => inv_reset,
                                     EN_count_value => en,
                                     count_value => count,
                                     RDY_count_value => open);

  GPIO_LED <= count;

end architecture behavioral;

