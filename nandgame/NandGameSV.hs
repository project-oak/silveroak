{- Copyright 2020 The Project Oak Authors
  
   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at
  
       http://www.apache.org/licenses/LICENSE-2.0
  
   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
-}

-- A program for writing out SystemVerilog netlists for some of the
-- circuit blocks described in the NandGame.v Cava descriptions.

module Main where

import Cava2SystemVerilog
import NandGame

main :: IO ()
main 
  = do writeSystemVerilog inverterNetlist
       writeSystemVerilog andgateNetlist
       writeSystemVerilog orgateNetlist
       writeSystemVerilog xorgateNetlist
       writeSystemVerilog halfAdderNetlist
       writeSystemVerilog fullAdderNetlist
