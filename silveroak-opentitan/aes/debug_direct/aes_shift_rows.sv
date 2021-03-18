// Cava auto-generated SystemVerilog. Do not hand edit.
module aes_shift_rows(
  input logic [3:0][3:0][7:0]data_i, 
  input logic op_i, 
  output logic [3:0][3:0][7:0]data_o
  );


logic [3:0][7:0]v0;
logic [3:0][7:0]v1;
logic [3:0][7:0]v2;
logic [3:0][7:0]v3;
logic [7:0]v4;
logic [7:0]v5;
logic [7:0]v6;
logic [7:0]v7;
logic [3:0][7:0]v8;
logic [7:0]v9;
logic [7:0]v10;
logic [7:0]v11;
logic [7:0]v12;
logic [3:0][7:0]v13;
logic [7:0]v14;
logic [7:0]v15;
logic [7:0]v16;
logic [7:0]v17;
logic [3:0][7:0]v18;
logic [1:0][3:0][7:0]v19;
logic [0:0]v20;
logic [3:0][7:0]v21;
logic [7:0]v22;
logic [7:0]v23;
logic [7:0]v24;
logic [7:0]v25;
logic [3:0][7:0]v26;
logic [7:0]v27;
logic [7:0]v28;
logic [7:0]v29;
logic [7:0]v30;
logic [3:0][7:0]v31;
logic [1:0][3:0][7:0]v32;
logic [0:0]v33;
logic [3:0][7:0]v34;
logic [3:0][3:0][7:0]v35;

  assign data_o = v35;
  assign v35 = {v34, v8, v21, v0};
  assign v34 = v32[v33];
  assign v33 = {op_i};
  assign v32 = {v31, v26};
  assign v31 = {v30, v29, v28, v27};
  assign v30 = v3[0];
  assign v29 = v3[3];
  assign v28 = v3[2];
  assign v27 = v3[1];
  assign v26 = {v25, v24, v23, v22};
  assign v25 = v3[2];
  assign v24 = v3[1];
  assign v23 = v3[0];
  assign v22 = v3[3];
  assign v21 = v19[v20];
  assign v20 = {op_i};
  assign v19 = {v18, v13};
  assign v18 = {v17, v16, v15, v14};
  assign v17 = v1[2];
  assign v16 = v1[1];
  assign v15 = v1[0];
  assign v14 = v1[3];
  assign v13 = {v12, v11, v10, v9};
  assign v12 = v1[0];
  assign v11 = v1[3];
  assign v10 = v1[2];
  assign v9 = v1[1];
  assign v8 = {v7, v6, v5, v4};
  assign v7 = v2[1];
  assign v6 = v2[0];
  assign v5 = v2[3];
  assign v4 = v2[2];
  assign v3 = data_i[3];
  assign v2 = data_i[2];
  assign v1 = data_i[1];
  assign v0 = data_i[0];

endmodule

