`default_nettype none
`timescale 1ns/10ps

module hack_clock(
    input clk,
    input reset, 
    output reg hack_clk,
    output reg strobe,
    output going_to_rise
);

reg [6:0] counter;

assign going_to_rise = counter==32 && ~hack_clk; 

always @(posedge clk) begin

    if(reset) begin
        hack_clk <= 0;
        counter <= 0; 
        strobe <= 0;

    end else begin
        counter <= counter + 1'b1;
        strobe <= 1'b0;
        if(counter==34) begin
            counter <= 0;
            strobe <= 1'b1;
            hack_clk <= ~hack_clk;
        end
    end

end

endmodule