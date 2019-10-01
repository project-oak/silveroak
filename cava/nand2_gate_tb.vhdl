entity nand2_gate_tb is
end entity nand2_gate_tb;

library ieee;
use ieee.std_logic_1164.all;
use work.nand2_gate_package.all;
architecture simulation of nand2_gate_tb is
  signal clk, rst, i0, i1, o : std_ulogic;
begin
  nand2_inst : nand2_gate port map (clk => clk, rst => rst,
                                    i0 => i0, i1 => i1, o => o);
  sim : process is
    begin
      rst <= '1';
      clk <= '0'; wait for 10 ns; clk <= '1'; wait for 10 ns;

      rst <= '0';
      i0 <= '0'; i1 <= '0';
      clk <= '0'; wait for 10 ns; clk <= '1'; wait for 10 ns;

      i0 <= '0'; i1 <= '1';
      clk <= '0'; wait for 10 ns; clk <= '1'; wait for 10 ns;

      i0 <= '1'; i1 <= '0';
      clk <= '0'; wait for 10 ns; clk <= '1'; wait for 10 ns;

      i0 <= '1'; i1 <= '1';
      clk <= '0'; wait for 10 ns; clk <= '1'; wait for 10 ns;

      clk <= '0'; wait for 10 ns; clk <= '1'; wait for 10 ns;
      clk <= '0'; wait for 10 ns; clk <= '1'; wait for 10 ns;

      wait;
  end process sim;
end architecture simulation;
