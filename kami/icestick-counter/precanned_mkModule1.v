

// CBG Orangepath HPR L/S System

// Verilog output file generated at 19/09/2019 07:20:55
// CBG-BSV TOY COMPILER VERSION 0.47 ALPHA 18th-Sept-2019
//  /home/djg11/d320/hprls/bsvc/priv_distro/lib/bsv.exe -incdir=/home/djg11/d320/hprls/bsvc/priv_distro/libs/camlib Counter4.bsv -g mkModule1 -vnl=dut.v
`timescale 1ns/1ns


module mkModule1(    
/* portgroup= abstractionName=nokind */
    output mkModule1_count_value_RDY,
    input mkModule1_count_value_EN,
    output reg [3:0] mkModule1_count_value_RV,
    
/* portgroup= abstractionName=nokind pi_name=shemits10 */

/* portgroup= abstractionName=L2590-vg pi_name=net2batchdirectoratenets10 */
input CLK,
    input RST_N);

function [3:0] rtl_unsigned_bitextract0;
   input [31:0] arg;
   rtl_unsigned_bitextract0 = $unsigned(arg[3:0]);
   endfunction

// abstractionName=nokind pi_name=sigmash10
  reg [3:0] mkModule1_counterReg_read_RV;
  reg mkModule1_counterReg_write_EN;
  reg [3:0] mkModule1_counterReg_write_din;
// abstractionName=nokind pi_name=mainmash10
  reg mkModule1_incrementAndOutput_FIRE;
 always   @(posedge CLK )  begin 
      //Start structure cvtToVerilogmkModule1/1.0
      if (!RST_N)  mkModule1_counterReg_read_RV <= 32'd0;
           else if (mkModule1_counterReg_write_EN)  mkModule1_counterReg_read_RV <= mkModule1_counterReg_write_din;
              //End structure cvtToVerilogmkModule1/1.0


       end 
      

assign mkModule1_count_value_RDY = 32'd1;

always @(*) mkModule1_incrementAndOutput_FIRE = RST_N;

always @(*) mkModule1_counterReg_write_EN = mkModule1_incrementAndOutput_FIRE;

always @(*) mkModule1_counterReg_write_din = rtl_unsigned_bitextract0(4'd1+mkModule1_counterReg_read_RV);

always @(*) mkModule1_count_value_RV = mkModule1_counterReg_read_RV;

// Structural Resource (FU) inventory for dut:// 2 vectors of width 1
// 2 vectors of width 4
// Total state bits in module = 10 bits.
// Total number of leaf cells = 0
endmodule

//  
// Layout wiring length estimation mode is LAYOUT_lcp.
//HPR L/S (orangepath) auxiliary reports.
//Toy Bluespec Compiler Compilation Report
//CBG-BSV TOY COMPILER VERSION 0.47 ALPHA 18th-Sept-2019
//19/09/2019 07:20:55
//Cmd line args:  /home/djg11/d320/hprls/bsvc/priv_distro/lib/bsv.exe -incdir=/home/djg11/d320/hprls/bsvc/priv_distro/libs/camlib Counter4.bsv -g mkModule1 -vnl=dut.v


//----------------------------------------------------------

//Report from bsvc:::
//Rule Ordering for Rule Group 'CC0'
//*------------------------------+--------+---------------+------------------+---------+-------------*
//| Rule Name                    | Counts | Nautral Order | Textual Ordering | Urgency | Final Order |
//*------------------------------+--------+---------------+------------------+---------+-------------*
//| mkModule1.incrementAndOutput | 1 1    | 0             | 0                |         | 0           |
//*------------------------------+--------+---------------+------------------+---------+-------------*

//----------------------------------------------------------

//Report from bsvc:::
//Rule Ordering for Rule Group 'CC1'
//*-----------------------+--------+---------------+------------------+---------+-------------*
//| Rule Name             | Counts | Nautral Order | Textual Ordering | Urgency | Final Order |
//*-----------------------+--------+---------------+------------------+---------+-------------*
//| mkModule1.count_value | 1 1    | 0             | 0                |         | 0           |
//*-----------------------+--------+---------------+------------------+---------+-------------*

//----------------------------------------------------------

//Report from bsvc:::
//Rule Partitions And Conflicts.
//*------+------------------------------+--------------*
//| Rule | Partition                    | Status Flags |
//*------+------------------------------+--------------*
//| CC0  | mkModule1.incrementAndOutput | --A-         |
//| CC1  | mkModule1.count_value        | --A-         |
//*------+------------------------------+--------------*

//----------------------------------------------------------

//Report from bsvc:::
//Rule Nominal Firing Rates.
//*------------------------------+--------+--------*
//| Rule                         | Target | Actual |
//*------------------------------+--------+--------*
//| mkModule1.count_value        | BLANK  | 0.50   |
//| mkModule1.incrementAndOutput | BLANK  | 1.00   |
//*------------------------------+--------+--------*

//----------------------------------------------------------

//Report from IP-XACT input/output:::
//Write IP-XACT component file for dut to dut.xml

//----------------------------------------------------------

//Report from verilog_render:::
//Structural Resource (FU) inventory for dut:
//2 vectors of width 1
//
//2 vectors of width 4
//
//Total state bits in module = 10 bits.
//
//Total number of leaf cells = 0
//

//Major Statistics Report:
// eof (HPR L/S Verilog)
