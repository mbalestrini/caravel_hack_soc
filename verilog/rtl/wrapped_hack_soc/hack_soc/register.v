`default_nettype none
`timescale 1ns/10ps

module register(input clk, input [D_WIDTH-1:0] in, input load, output [D_WIDTH-1:0] out);
	parameter D_WIDTH = 16;
	
	reg [D_WIDTH-1:0] data;
	
	assign out=data;
	
	always @(posedge clk) 
	begin
		if(load) begin
			data <= in;
		end		
	end
	
endmodule