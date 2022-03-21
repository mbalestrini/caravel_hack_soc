`default_nettype none
`timescale 1ns/10ps

module hack_alu(	input [D_WIDTH-1:0] x, input [D_WIDTH-1:0] y, 
			input zx, input nx, input zy, input ny, input f, input no, 
			output [D_WIDTH-1:0] out, output zr, output ng);

	parameter D_WIDTH = 16;

	wire [D_WIDTH-1:0] vzx;
	wire [D_WIDTH-1:0] vnx;
	wire [D_WIDTH-1:0] vzy;
	wire [D_WIDTH-1:0] vny;
	wire [D_WIDTH-1:0] vf;
	
	
	assign vzx = (zx==1 ? 0 : x);
	assign vnx = (nx==1 ? ~vzx : vzx);
	
	assign vzy = (zy==1 ? 0 : y);
	assign vny = (ny==1 ? ~vzy : vzy);
	
	assign vf = (f==1 ? vnx + vny : vnx & vny);
	assign out = (no==1 ? ~vf : vf);
	
	assign zr = ~(|out);
	assign ng = out[D_WIDTH-1];
endmodule

