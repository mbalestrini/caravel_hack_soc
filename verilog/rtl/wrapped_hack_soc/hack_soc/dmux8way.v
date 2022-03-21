`default_nettype none
`timescale 1ns/10ps

module dmux8way(input [D_WIDTH-1:0] in, 
				input [2:0] sel, 
				output [D_WIDTH-1:0] a, 
				output [D_WIDTH-1:0] b,
				output [D_WIDTH-1:0] c,
				output [D_WIDTH-1:0] d,
				output [D_WIDTH-1:0] e,
				output [D_WIDTH-1:0] f,
				output [D_WIDTH-1:0] g,
				output [D_WIDTH-1:0] h
				);
	parameter D_WIDTH = 1;
	
	assign a = (sel=='b000 ? in : 0);
	assign b = (sel=='b001 ? in : 0);
	assign c = (sel=='b010 ? in : 0);
	assign d = (sel=='b011 ? in : 0);
	assign e = (sel=='b100 ? in : 0);
	assign f = (sel=='b101 ? in : 0);
	assign g = (sel=='b110 ? in : 0);
	assign h = (sel=='b111 ? in : 0);
endmodule