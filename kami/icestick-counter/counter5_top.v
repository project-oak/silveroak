module counter5_top (
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

    reg [4:0] count;
    wire reset = 1'b1;
    wire en = 1'b1;
    wire rdy;

    reg [22:0] slowdown = 23'b0;

    always @(posedge clk) begin
        slowdown++;
    end

    mkModule1 COUNTER (
        .CLK(slowdown[22]),
        .RST_N(reset),
        .EN_count_value(en),
        .RDY_count_value(rdy),
        .count_value(count)
    );

    assign led1 = count[0];
    assign led2 = count[1];
    assign led3 = count[2];
    assign led4 = count[3];
    assign led5 = count[4];

endmodule
