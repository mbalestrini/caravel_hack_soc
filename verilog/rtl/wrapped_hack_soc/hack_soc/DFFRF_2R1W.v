`default_nettype none
`timescale 1ns/10ps

`ifndef FORMAL
(* blackbox *)
`endif
module DFFRF_2R1W (
`ifdef USE_POWER_PINS
    inout vccd1,  
    inout vssd1,  
`endif
    input CLK,
    
    output [31:0] DA,
    output [31:0] DB,
    input [31:0] DW,
    input [4:0] RA,
    input [4:0] RB,
    input [4:0] RW,    
    input WE
); 



reg [31:0] RAM[ 31 : 0];

assign DA = RAM[RA];
assign DB = RAM[RB];



always @(posedge CLK) begin
    if (WE) begin
        RAM[RW] <= DW;
    end
end



endmodule

