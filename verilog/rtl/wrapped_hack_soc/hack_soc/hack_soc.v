`default_nettype none
`timescale 1ns/10ps

module hack_soc (
	input clk,
	input display_clk,
	input reset,
	input hack_external_reset,

	// ** RAM: qspi serial sram **/
	output ram_cs_n,
	output ram_sck,
	output ram_sio_oe, // output enable the SIO lines
	// SIO as inputs from SRAM	
	input ram_sio0_i, // sram_si_sio0 
	input ram_sio1_i, // sram_so_sio1
	input ram_sio2_i, // sram_sio2
	input ram_sio3_i, // sram_hold_n_sio3
	// SIO as outputs to SRAM
	output ram_sio0_o, // sram_si_sio0
	output ram_sio1_o, // sram_so_sio1
	output ram_sio2_o, // sram_sio2
	output ram_sio3_o, // sram_hold_n_sio3


	// ** ROM: qspi serial sram **/
	output rom_cs_n,
	output rom_sck,
	output rom_sio_oe, // output enable the SIO lines
	// SIO as inputs from SRAM	
	input rom_sio0_i, // sram_si_sio0 
	input rom_sio1_i, // sram_so_sio1
	input rom_sio2_i, // sram_sio2
	input rom_sio3_i, // sram_hold_n_sio3
	// SIO as outputs to SRAM
	output rom_sio0_o, // sram_si_sio0
	output rom_sio1_o, // sram_so_sio1
	output rom_sio2_o, // sram_sio2
	output rom_sio3_o, // sram_hold_n_sio3



	// ** VRAM: qspi serial sram **/
	output vram_cs_n,
	output vram_sck,
	output vram_sio_oe, // output enable the SIO lines
	// SIO as inputs from SRAM	
	input vram_sio0_i, // sram_si_sio0 
	input vram_sio1_i, // sram_so_sio1
	input vram_sio2_i, // sram_sio2
	input vram_sio3_i, // sram_hold_n_sio3
	// SIO as outputs to SRAM
	output vram_sio0_o, // sram_si_sio0
	output vram_sio1_o, // sram_so_sio1
	output vram_sio2_o, // sram_sio2
	output vram_sio3_o, // sram_hold_n_sio3



	// ** DISPLAY ** //
	output display_hsync,
	output display_vsync,
	output display_rgb,


	// ** KEYBOARD ** //
	input [7:0] keycode,

	// ** GPIO ** //
	input  		[HACK_GPIO_I_WIDTH-1:0] gpio_i,
	output reg 	[HACK_GPIO_O_WIDTH-1:0] gpio_o,


	// ROM LOADING LINES
	input rom_loader_load,
	input rom_loader_sck,
	input [INSTRUCTION_WIDTH-1:0] rom_loader_data,
	output rom_loader_ack
	

	// DEBUG nets
	// output [ROM_ADDRESS_WIDTH-1:0] debug_pc,
	// output [RAM_ADDRESS_WIDTH-1:0] debug_addressM,
	// output [INSTRUCTION_WIDTH-1:0] debug_instruction,
	// output reg [WORD_WIDTH-1:0] debug_gpio

	);


//*******************************************************************************************
// Main project parameters 
//*******************************************************************************************
parameter WORD_WIDTH = 16; 
parameter RAM_WORDS = 32768; // 2^A_WIDTH
parameter RAM_ADDRESS_WIDTH = $clog2(RAM_WORDS);
parameter ROM_WORDS = 32768; // 2^A_WIDTH
parameter ROM_ADDRESS_WIDTH = $clog2(ROM_WORDS);
parameter INSTRUCTION_WIDTH = WORD_WIDTH;
parameter VRAM_WORDS = 8192;
parameter VRAM_ADDRESS_WIDTH = $clog2(VRAM_WORDS);

// Address Mapping
parameter [RAM_ADDRESS_WIDTH-1:0] HACK_ADDRESS_VRAM_START = 16384;
parameter [RAM_ADDRESS_WIDTH-1:0 ]HACK_ADDRESS_VRAM_END = 24575;
parameter [RAM_ADDRESS_WIDTH-1:0] HACK_ADDRESS_KEYBOARD = 'h6000;
parameter [RAM_ADDRESS_WIDTH-1:0] HACK_ADDRESS_GPIO_I = 'h6001;
parameter [RAM_ADDRESS_WIDTH-1:0] HACK_ADDRESS_GPIO_O = 'h6002;

parameter SRAM_ADDRESS_WIDTH = 24;

parameter HACK_GPIO_WIDTH = 8;
parameter HACK_GPIO_I_WIDTH = 4;
parameter HACK_GPIO_O_WIDTH = 4;

parameter HACK_SCREEN_WIDTH = 512;
parameter HACK_SCREEN_HEIGHT = 256;
parameter HACK_SCREEN_H_OFFSET = 64;//64;
parameter HACK_SCREEN_V_OFFSET = 112;




reg [1:0] hack_wait_clocks;
reg rom_loading_process;


wire hack_clk_strobe;
wire hack_clk_going_to_rise;
hack_clock hack_clock_0(
	.clk(clk),
	.reset(reset),
	.hack_clk(hack_clk),
	.strobe(hack_clk_strobe),
	.going_to_rise(hack_clk_going_to_rise)
);


wire hack_clk;
wire hack_reset;
wire [RAM_ADDRESS_WIDTH-1:0] hack_addressM;
wire hack_writeM;
wire [WORD_WIDTH-1:0] hack_inM;
wire [WORD_WIDTH-1:0] hack_outM;
wire [INSTRUCTION_WIDTH-1:0] hack_instruction;
wire [ROM_ADDRESS_WIDTH-1:0] hack_pc;
reg hack_rom_request;
hack_cpu #(
		.WORD_WIDTH(WORD_WIDTH),
		.INSTRUCTION_WIDTH(INSTRUCTION_WIDTH),
		.RAM_ADDRESS_WIDTH(RAM_ADDRESS_WIDTH),
		.ROM_ADDRESS_WIDTH(ROM_ADDRESS_WIDTH)
	) cpu (
		.clk(hack_clk), 
		.inM(hack_inM), 
		.instruction(hack_instruction), 
		.reset(hack_reset),
		.outM(hack_outM), 
		.writeM(hack_writeM), 
		.addressM(hack_addressM), 
		.pc(hack_pc)
		);



wire rom_loader_request;
wire [INSTRUCTION_WIDTH-1:0] rom_loader_output_data;
wire [ROM_ADDRESS_WIDTH-1:0] rom_loader_output_address;

rom_stream_loader #(.DATA_WIDTH(INSTRUCTION_WIDTH), .ADDRESS_WIDTH(ROM_ADDRESS_WIDTH)) 
	rom_loader(
		.clk(clk),
		.reset(reset),
		// Loader nets
		.load(rom_loading_process), //rom_loader_load),
		.input_data(rom_loader_data),
		.sck(rom_loader_sck),
		.ack(rom_loader_ack),
		// ROM nets
		.rom_busy(rom_busy),
		.rom_initialized(rom_initialized),
		.rom_request(rom_loader_request),
		.output_data(rom_loader_output_data),
		.output_address(rom_loader_output_address)				
);



// inputs to spi_sram_encoder
wire ram_request;
reg ram_step1_write_request;
reg ram_step2_read_request;

// outputs from spi_sram_encoder
wire ram_busy;
wire ram_initialized;
wire ram_write_enable;
wire [WORD_WIDTH-1:0] ram_data_out;

reg [RAM_ADDRESS_WIDTH-1:0] synch_hack_addressM;
reg synch_hack_writeM;
reg [WORD_WIDTH-1:0] synch_hack_outM;

// always @(posedge hack_clk ) begin
// 	synch_hack_writeM <= hack_writeM;
// 	synch_hack_outM <= hack_outM;
// end




always @(posedge clk ) begin
	ram_step1_write_request <= 0;

	ram_step2_read_request <= 0;

	if(hack_clk_going_to_rise) begin
		synch_hack_outM <= 0;
		if(hack_writeM) begin
			synch_hack_writeM <= hack_writeM;
			synch_hack_outM <= hack_outM;
			synch_hack_addressM <= hack_addressM;
			ram_step1_write_request <= 1;
		end
	end else if(hack_clk_strobe && ~hack_clk) begin
		ram_step1_write_request <= 0;
		ram_step2_read_request <= 1;
		synch_hack_writeM <= 0;
		synch_hack_addressM <= hack_addressM;
		synch_hack_outM <= 0;

	end
end


spi_sram_encoder #(	.WORD_WIDTH(WORD_WIDTH), .ADDRESS_WIDTH(RAM_ADDRESS_WIDTH) )
		ram_encoder_0
		(
			.clk(clk),
			.reset(reset), 

			.request(ram_request),
			.busy(ram_busy),
			.initialized(ram_initialized),
			
			.address(synch_hack_addressM),
			.write_enable(ram_write_enable),
			.data_in(ram_data_out),
			.data_out(synch_hack_outM),

			.sram_cs_n(ram_cs_n),
			.sram_sck(ram_sck),

			.sram_sio_oe(ram_sio_oe),

			.sram_sio0_i(ram_sio0_i), 
			.sram_sio1_i(ram_sio1_i), 
			.sram_sio2_i(ram_sio2_i), 
			.sram_sio3_i(ram_sio3_i), 

			.sram_sio0_o(ram_sio0_o), 
			.sram_sio1_o(ram_sio1_o), 
			.sram_sio2_o(ram_sio2_o), 
			.sram_sio3_o(ram_sio3_o) 
		);


// inputs to spi_sram_encoder
wire rom_request;
wire [ROM_ADDRESS_WIDTH-1:0] rom_address;
// outputs from spi_sram_encoder
wire rom_busy;
wire rom_initialized;
wire rom_write_enable;
// wire [INSTRUCTION_WIDTH-1:0] rom_data_out = {INSTRUCTION_WIDTH{1'b0}};



spi_sram_encoder #(	.WORD_WIDTH(INSTRUCTION_WIDTH), .ADDRESS_WIDTH(ROM_ADDRESS_WIDTH) )
		rom_encoder_0
		(
			.clk(clk),
			.reset(reset), 

			.request(rom_request),
			.busy(rom_busy),
			.initialized(rom_initialized),
			
			.address(rom_address),
			.write_enable(rom_write_enable), 
			.data_in(hack_instruction),
			.data_out(rom_loader_output_data),

			.sram_cs_n(rom_cs_n),
			.sram_sck(rom_sck),

			.sram_sio_oe(rom_sio_oe),

			.sram_sio0_i(rom_sio0_i), 
			.sram_sio1_i(rom_sio1_i), 
			.sram_sio2_i(rom_sio2_i), 
			.sram_sio3_i(rom_sio3_i), 

			.sram_sio0_o(rom_sio0_o), 
			.sram_sio1_o(rom_sio1_o), 
			.sram_sio2_o(rom_sio2_o), 
			.sram_sio3_o(rom_sio3_o) 
		);





wire pixel_value;
wire vram_initialized;
wire vram_write_enable;
wire [VRAM_ADDRESS_WIDTH-1:0] vram_write_address;
spi_video_ram_2 #(
	.WORD_WIDTH(WORD_WIDTH),
    .VRAM_ADDRESS_WIDTH(VRAM_ADDRESS_WIDTH),
    .SRAM_ADDRESS_WIDTH(SRAM_ADDRESS_WIDTH),
    .HACK_SCREEN_WIDTH(HACK_SCREEN_WIDTH),
    .HACK_SCREEN_HEIGHT(HACK_SCREEN_HEIGHT),
    .HACK_SCREEN_H_OFFSET(HACK_SCREEN_H_OFFSET),
    .HACK_SCREEN_V_OFFSET(HACK_SCREEN_V_OFFSET)
) spi_video_ram_1 (
    .clk(clk),
	.reset(reset), 	

	.initialized(vram_initialized), 


    // VIDEO VRAM READ
	.clks_before_active(display_clks_before_active),
    .display_active(display_active),
    .display_hpos(display_hpos),
    .display_vpos(display_vpos),
	.pixel_out(pixel_value),
	

    // HACK VRAM WRITE
	.hack_clk_rise_edge(hack_clk_strobe & hack_clk),
	.hack_outM(hack_outM),
    .hack_addressM(vram_write_address),
    .hack_writeM(vram_write_enable),


    // Serial SRAM nets 
	.sram_cs_n(vram_cs_n),
	.sram_sck(vram_sck),

	.sram_sio_oe(vram_sio_oe), // output enable the SIO lines
	// SIO as inputs from SRAM	
	.sram_sio0_i(vram_sio0_i), // sram_si_sio0 
	.sram_sio1_i(vram_sio1_i), // sram_so_sio1
	.sram_sio2_i(vram_sio2_i), // sram_sio2
	.sram_sio3_i(vram_sio3_i), // sram_hold_n_sio3
	// SIO as outputs to SRAM
	.sram_sio0_o(vram_sio0_o), // sram_si_sio0
	.sram_sio1_o(vram_sio1_o), // sram_so_sio1
	.sram_sio2_o(vram_sio2_o), // sram_sio2
	.sram_sio3_o(vram_sio3_o) // sram_hold_n_sio3

);





// VIDEO GENERATOR
wire [9:0] display_hpos;
wire [9:0] display_vpos;
wire display_active;
wire [9:0] display_clks_before_active;
wire reset_display = reset; //hack_reset; //reset;
// assign display_rgb = display_hpos[2] || display_vpos[2];
video_signal_generator_640x480 video_generator_1 (
	//i_clk,           // base clock
	.i_pix_stb(display_clk),       // pixel clock strobe
	.i_rst(reset_display),           // reset: restarts frame
	.o_hs(display_hsync),           // horizontal sync
	.o_vs(display_vsync),           // vertical sync
	// .o_blanking(),     // high during blanking interval
	.o_active(display_active),       // high during active pixel drawing
	// .o_screenend(),    // high for one tick at the end of screen
	// .o_animate(),      // high for one tick at end of active drawing
	.o_x(display_hpos),      // current pixel x position
	.o_y(display_vpos),       // current pixel y position
	.o_clks_before_active(display_clks_before_active)
);





// ** Memory Address Mapping ** //
wire mapping_is_ram_address = hack_addressM < HACK_ADDRESS_VRAM_START;
wire mapping_is_vram_address = (hack_addressM >= HACK_ADDRESS_VRAM_START) && (hack_addressM <= HACK_ADDRESS_VRAM_END);
wire mapping_is_ram_or_vram_address = hack_addressM <= HACK_ADDRESS_VRAM_END;
wire mapping_is_keyboard_address = (hack_addressM==HACK_ADDRESS_KEYBOARD);
wire mapping_is_gpio_i_address = (hack_addressM==HACK_ADDRESS_GPIO_I);
wire mapping_is_gpio_o_address = (hack_addressM==HACK_ADDRESS_GPIO_O);


// assign ram_request = !hack_reset && ram_initialized && !ram_busy && hack_clk_strobe && hack_clk;
// assign ram_request = !hack_reset && ram_initialized && !ram_busy && hack_clk_strobe;
assign ram_request = !hack_reset && ram_initialized && !ram_busy && (ram_step1_write_request || ram_step2_read_request) ;
// assign hack_rom_request = rom_initialized && !rom_busy && hack_clk_strobe && hack_clk;
always @(posedge clk ) begin
	hack_rom_request <= 0;
	if(hack_clk_strobe && ~hack_clk) begin
		hack_rom_request <= rom_initialized && !rom_busy ;//&& hack_clk_strobe && hack_clk;	
	end
end

assign rom_request = rom_loading_process ? rom_loader_request : hack_rom_request;

assign rom_write_enable = (rom_loading_process);// && rom_loader_request);
assign ram_write_enable = !hack_reset && synch_hack_writeM && mapping_is_ram_or_vram_address;
assign vram_write_enable = !hack_reset && hack_clk_strobe && hack_writeM && mapping_is_vram_address;

assign rom_address = rom_loading_process ? rom_loader_output_address : hack_pc;
assign vram_write_address = hack_addressM[VRAM_ADDRESS_WIDTH-1:0];

assign hack_inM = (mapping_is_ram_or_vram_address) ? ram_data_out : /* ram & vram */
					(hack_addressM == HACK_ADDRESS_KEYBOARD) ? { {(WORD_WIDTH-8){1'b0}}, keycode} :  /*keyboard*/
					mapping_is_gpio_i_address ? { {(WORD_WIDTH-HACK_GPIO_O_WIDTH){1'b0}},gpio_i_stored} : /* GPIO_I */
					mapping_is_gpio_o_address ? { {(WORD_WIDTH-HACK_GPIO_O_WIDTH){1'b0}}, gpio_o} : /* GPIO_O */
					0;


assign hack_reset = rom_loading_process || hack_external_reset || (hack_wait_clocks!=0) || reset || !ram_initialized || !rom_initialized || !vram_initialized;


assign display_rgb = display_active ? (hack_reset ? logo_pixel : pixel_value) : 0 ;


wire logo_pixel;
reg [4:0] boot_loading_offset;

//assign boot_loading_offset = rom_loader_data[3:0];// rom_loading_process ? rom_loader_data[9:0] : 0;

always @(posedge clk ) begin
	if(reset) begin
		boot_loading_offset <= 0;
	end else begin
		if(rom_loading_process && rom_loader_sck) 
			boot_loading_offset <= boot_loading_offset + 1;	
	end
end

boot_logo boot_logo_1 (
	.hpos(display_hpos),
	.vpos(display_vpos),
	.pixel(logo_pixel)
	 ,	.loading_offset(boot_loading_offset)

);


always @(posedge clk ) begin
	if(rom_loader_load) begin
		if(hack_reset || (hack_clk_strobe && hack_clk)) begin
			rom_loading_process <= 1'b1;
		end
	end else begin
		rom_loading_process <= 1'b0;
	end
end

always @(posedge clk ) begin
	if(reset) begin
		hack_wait_clocks <= 2;
	end else begin

		if(hack_external_reset || rom_loading_process) begin
			hack_wait_clocks <= 2;
		end else if(hack_wait_clocks!=0 && hack_clk_strobe && hack_clk) begin 
			hack_wait_clocks <= hack_wait_clocks - 2'b1;
		end
	end
	
end




// GPIO_O
always @(posedge hack_clk) begin
	if(hack_reset) begin
		gpio_o <= 0;
	end else begin
		if(mapping_is_gpio_o_address && hack_writeM) begin
			gpio_o <= hack_outM[HACK_GPIO_O_WIDTH-1:0];
		end
	end
end

// GPIO_I
reg [HACK_GPIO_I_WIDTH-1:0] gpio_i_stored;
always @(posedge hack_clk) begin
	if(hack_reset) begin
		gpio_i_stored <= 0;
	end else begin
		if(mapping_is_gpio_i_address && ~hack_writeM) begin
			gpio_i_stored <= gpio_i;
		end
	end
end






`ifdef FORMAL
    // register for knowing if we have just started
    reg f_past_valid = 0;
	reg initial_reset_passed = 0;

	
	// start in reset
    initial assume(reset);
	initial assume(rom_loader_load==0);
	initial assume(hack_wait_clocks==2);
		

    // The clock toggles.
    reg last_clk = 1'b0;
    always @($global_clock) begin
        assume (clk == !last_clk);
        last_clk <= clk;

		f_past_valid <= 1;

		// Disable loading ROMs formal verification for now
		assume(rom_loader_load==0);
        assume(hack_external_reset==0);


		if(f_past_valid) begin
			if(initial_reset_passed) begin
				assume(reset==0);								
			end
		end
    end




	always @(negedge clk) begin
		
    end



    always @(posedge clk) begin 
		if(initial_reset_passed) begin

			//assume(reset==0);

			COVER_RAM_INIT: cover(ram_initialized);
			COVER_ROM_INIT: cover(rom_initialized);
			COVER_VRAM_INIT: cover(vram_initialized);

			ASSERT_WAIT_CLOCK_BOUNDARIES: assert(hack_wait_clocks<=2);	

			if(!ram_initialized) begin
				ASSERT_RAM_REQUESTS_ON_INIT: assert(ram_request==0);
			end
			if(!rom_initialized) begin
				ASSERT_ROM_REQUESTS_ON_INIT: assert(rom_request==0);
			end


			if($past(ram_request) && !hack_reset && $rose(hack_clk)) begin
				ASSERT_RAM_CLK_SYNCHRO: assert($rose(ram_sck));
			end
		end
	
		if(f_past_valid) begin
			COVER_HACK_CLOCK_START: cover($rose(hack_clk));			
			if($fell(reset)) begin
				initial_reset_passed <= 1;
			end			
		end

    end

`endif   		

endmodule