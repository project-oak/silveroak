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
entity and2_tb is
end entity and2_tb;

use std.textio.all;
use work.and2_package.all;
architecture behavioural of and2_tb is
   signal a, b, c : bit;
begin
 and2_instance : and2 port map (a, b, c);
 test : process is
   variable l : line;
 begin
   a <= '0'; b <='0'; wait for 10 ns; write (l, c); writeline (output, l);
   a <= '1'; b <='1'; wait for 10 ns; write (l, c); writeline (output, l);
             b <='0'; wait for 10 ns; write (l, c); writeline (output, l);
   wait;
 end process test;

end architecture behavioural ;