`default_nettype none
`timescale 1ns/10ps

module pc(input clk, input reset, input [D_WIDTH-1:0] in, input load, input inc, output [D_WIDTH-1:0] out);
	parameter D_WIDTH = 16; // WORD SIZE
	
	wire [D_WIDTH-1:0] pc_in;
	wire [D_WIDTH-1:0] pc_out;
	wire pc_load;
	register #(.D_WIDTH(D_WIDTH)) REG (.clk(clk), .in(pc_in), .load(pc_load), .out(pc_out));
	
	assign out = pc_out;
	assign pc_load = 1'b1;
	assign pc_in = (reset ? {D_WIDTH{1'b0}} : 
				((load) ? in :	
				((inc) ? pc_out + 1 :	
				pc_out)));					


endmodule
