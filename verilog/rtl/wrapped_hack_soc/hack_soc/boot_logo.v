`default_nettype none
`timescale 1ns/10ps

module boot_logo(
	input [9:0] hpos,
	input [9:0] vpos,
	output pixel,	
	input [9:0] loading_offset
);

localparam SCALE = 1;
localparam LOGO_WIDTH = 16*SCALE;
localparam LOGO_HEIGHT = 19*SCALE;
localparam LOGO_START_H = (640-LOGO_WIDTH)/2;
localparam LOGO_START_V = (480-LOGO_HEIGHT)/2;

wire [9:0] hlogo = (hpos - LOGO_START_H)/SCALE;
wire [9:0] vlogo = (vpos - LOGO_START_V)/SCALE;

wire [9:0] vlogo_with_offset = (vlogo > 0 && vlogo<8) ? vlogo + loading_offset*SCALE : vlogo;


wire in_logo_area = (hpos >= LOGO_START_H) & (hpos < (LOGO_START_H+LOGO_WIDTH)) & (vpos >= LOGO_START_V) & (vpos < (LOGO_START_V+LOGO_HEIGHT));


assign pixel = in_logo_area  ? ~LOGO[ ( ((LOGO_HEIGHT/SCALE-vlogo_with_offset)<<4) - hlogo)] : 1;

// reg [15:0] logo [0:17] = {
parameter LOGO = {
	16'b0111111111111110,
	16'b0100000000000010,
	16'b0101111101000010,
	16'b0100000000000010,
	16'b0101010111001010,
	16'b0100000000000010,
	16'b0101011000011010,
	16'b0100000000000010,
	16'b0111111111111110,
	16'b0000111111110000,
	16'b0111111111111110,
	16'b0111111111111010,
	16'b0111111111111110,
	16'b0111111111111110,	
	16'b0000000000000000,
	16'b0101011101101010,
	16'b0101010101001100,
	16'b0111011101001010,
	16'b0101010101101010
	};


// wire index = 
endmodule
/*



*/