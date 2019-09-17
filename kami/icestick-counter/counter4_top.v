module counter4_top (
    input  clki,
    output led1,
    output led2,
    output led3,
    output led4,
    output led5
);

    SB_GB clk_gb (
        .USER_SIGNAL_TO_GLOBAL_BUFFER(clki),
        .GLOBAL_BUFFER_OUTPUT(clk)
    );

    reg [3:0] count;
    wire reset = 1'b1;
    wire en = 1'b1;
    wire rdy;

    reg [20:0] slowdown = 9'b0;

    always @(posedge clk) begin
        slowdown++;
    end

    mkModule1 COUNTER (
        .CLK(slowdown[20]),
        .RST_N(reset),
        .EN_count_value(en),
        .count_value(count),
        .RDY_count_value(rdy)
    );

    assign led5 = 1'b1;
    assign led1 = count[0];
    assign led2 = count[1];
    assign led3 = count[2];
    assign led4 = count[3];

endmodule
