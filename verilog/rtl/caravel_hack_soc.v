`default_nettype none

`ifdef FORMAL
    `define MPRJ_IO_PADS 38    
`endif


module caravel_hack_soc(
`ifdef USE_POWER_PINS
    inout vdd,	// User area 1 1.8V supply
    inout vss,	// User area 1 digital ground
`endif

    // Wishbone Slave ports (WB MI A)
    input wb_clk_i,
    input wb_rst_i,
    input wbs_stb_i,
    input wbs_cyc_i,
    input wbs_we_i,
    input [3:0] wbs_sel_i,
    input [31:0] wbs_dat_i,
    input [31:0] wbs_adr_i,
    output wbs_ack_o,
    output [31:0] wbs_dat_o,

    // Logic Analyzer Signals
    input  [63:0] la_data_in,
    output [63:0] la_data_out,
    input  [63:0] la_oenb,

    // IOs
    input  [`MPRJ_IO_PADS-1:0] io_in,
    output [`MPRJ_IO_PADS-1:0] io_out,
    output [`MPRJ_IO_PADS-1:0] io_oeb,

    // IRQ
    output [2:0] irq
);

    // IO
    // permanently set oeb so that outputs are always enabled: 0 is output, 1 is high-impedance
    assign io_oeb[7:0] = {8{1'b0}};
    // assign io_oeb = {`MPRJ_IO_PADS{1'b0}};


    wire clk = wb_clk_i;

    // Logic Analyzer    
    wire hack_soc_reset = la_data_in[0];
    wire [7:0] keycode = la_data_in[8:1];
    wire rom_loader_sck = la_data_in[9];
    wire rom_loader_load = la_data_in[10];
    wire [15:0] rom_loader_data = la_data_in[26:11];
    wire rom_loader_ack;
    assign la_data_out[27] = rom_loader_ack;
    wire hack_external_reset_from_la = la_data_in[28];
    


    // ram
    wire ram_cs_n;
    wire ram_sck;
    wire ram_sio_oe;
    wire ram_sio0_o;
    wire ram_sio1_o;
    wire ram_sio2_o;
    wire ram_sio3_o;
    wire ram_sio0_i;
    wire ram_sio1_i;
    wire ram_sio2_i;
    wire ram_sio3_i;
    
    assign io_oeb[8] = 1'b0;
    assign io_out[8] = ram_cs_n;    
    assign io_oeb[9] = 1'b0;
    assign io_out[9] = ram_sck;     
    assign io_oeb[13:10] = {~ram_sio_oe, ~ram_sio_oe, ~ram_sio_oe, ~ram_sio_oe};
    assign io_out[13:10] = {ram_sio3_o, ram_sio2_o, ram_sio1_o, ram_sio0_o};
    assign {ram_sio3_i, ram_sio2_i, ram_sio1_i, ram_sio0_i} = io_in[13:10];

    // rom
    wire rom_cs_n;
    wire rom_sck;
    wire rom_sio_oe;
    wire rom_sio0_o;
    wire rom_sio1_o;
    wire rom_sio2_o;
    wire rom_sio3_o;
    wire rom_sio0_i;
    wire rom_sio1_i;
    wire rom_sio2_i;
    wire rom_sio3_i;

    assign io_oeb[14] = 1'b0;
    assign io_out[14] = rom_cs_n;    
    assign io_oeb[15] = 1'b0;
    assign io_out[15] = rom_sck;     
    assign io_oeb[19:16] = {~rom_sio_oe, ~rom_sio_oe, ~rom_sio_oe, ~rom_sio_oe};
    assign io_out[19:16] = {rom_sio3_o, rom_sio2_o, rom_sio1_o, rom_sio0_o};
    assign {rom_sio3_i, rom_sio2_i, rom_sio1_i, rom_sio0_i} = io_in[19:16];


    // vram
    wire vram_cs_n;
    wire vram_sck;
    wire vram_sio_oe;
    wire vram_sio0_o;
    wire vram_sio1_o;
    wire vram_sio2_o;
    wire vram_sio3_o;
    wire vram_sio0_i;
    wire vram_sio1_i;
    wire vram_sio2_i;
    wire vram_sio3_i;
    
    assign io_oeb[20] = 1'b0;
    assign io_out[20] = vram_cs_n;    
    assign io_oeb[21] = 1'b0;
    assign io_out[21] = vram_sck;     
    assign io_oeb[25:22] = {~vram_sio_oe, ~vram_sio_oe, ~vram_sio_oe, ~vram_sio_oe};
    assign io_out[25:22] = {vram_sio3_o, vram_sio2_o, vram_sio1_o, vram_sio0_o};
    assign {vram_sio3_i, vram_sio2_i, vram_sio1_i, vram_sio0_i} = io_in[25:22];


    wire hack_external_reset_from_io;
    assign io_oeb[26] = 1'b1;
    assign hack_external_reset_from_io = io_in[26];

    // hack_external_reset
    wire hack_external_reset;
    assign hack_external_reset = hack_external_reset_from_la | hack_external_reset_from_io;


    // display
    wire display_vsync;
    wire display_hsync;
    wire display_rgb;

    assign io_oeb[27] = 1'b0;
    assign io_out[27] = display_vsync;
    assign io_oeb[28] = 1'b0;
    assign io_out[28] = display_hsync;
    assign io_oeb[29] = 1'b0;
    assign io_out[29] = display_rgb;
    

    // GPIO
    wire [3:0] gpio_i;
    wire [3:0] gpio_o;
	assign io_oeb[33:30] = 4'b1111;
    assign gpio_i = io_in[33:30];
	assign io_oeb[37:34] = 4'b0000;
	assign io_out[37:34] = gpio_o;

    hack_soc soc(
        .clk(clk),
        .display_clk(clk),
        .reset(hack_soc_reset),

        .hack_external_reset(hack_external_reset),


        /** RAM: qspi serial sram **/
        .ram_cs_n(ram_cs_n),
        .ram_sck(ram_sck),
        .ram_sio_oe(ram_sio_oe), // output enable the SIO lines
        // SIO as inputs from SRAM	
        .ram_sio0_i(ram_sio0_i), // sram_si_sio0 
        .ram_sio1_i(ram_sio1_i), // sram_so_sio1
        .ram_sio2_i(ram_sio2_i), // sram_sio2
        .ram_sio3_i(ram_sio3_i), // sram_hold_n_sio3
        // SIO as outputs to SRAM
        .ram_sio0_o(ram_sio0_o), // sram_si_sio0
        .ram_sio1_o(ram_sio1_o), // sram_so_sio1
        .ram_sio2_o(ram_sio2_o), // sram_sio2
        .ram_sio3_o(ram_sio3_o), // sram_hold_n_sio3

        /** ROM: qspi serial sram **/
        .rom_cs_n(rom_cs_n),
        .rom_sck(rom_sck),
        .rom_sio_oe(rom_sio_oe), // output enable the SIO lines
        // SIO as inputs from SRAM	
        .rom_sio0_i(rom_sio0_i), // sram_si_sio0 
        .rom_sio1_i(rom_sio1_i), // sram_so_sio1
        .rom_sio2_i(rom_sio2_i), // sram_sio2
        .rom_sio3_i(rom_sio3_i), // sram_hold_n_sio3
        // SIO as outputs to SRAM
        .rom_sio0_o(rom_sio0_o), // sram_si_sio0
        .rom_sio1_o(rom_sio1_o), // sram_so_sio1
        .rom_sio2_o(rom_sio2_o), // sram_sio2
        .rom_sio3_o(rom_sio3_o), // sram_hold_n_sio3


        /** VRAM: qspi serial sram **/
        .vram_cs_n(vram_cs_n),
        .vram_sck(vram_sck),
        .vram_sio_oe(vram_sio_oe), // output enable the SIO lines
        // SIO as inputs from SRAM	
        .vram_sio0_i(vram_sio0_i), // sram_si_sio0 
        .vram_sio1_i(vram_sio1_i), // sram_so_sio1
        .vram_sio2_i(vram_sio2_i), // sram_sio2
        .vram_sio3_i(vram_sio3_i), // sram_hold_n_sio3
        // SIO as outputs to SRAM
        .vram_sio0_o(vram_sio0_o), // sram_si_sio0
        .vram_sio1_o(vram_sio1_o), // sram_so_sio1
        .vram_sio2_o(vram_sio2_o), // sram_sio2
        .vram_sio3_o(vram_sio3_o), // sram_hold_n_sio3

        // ** DISPLAY ** //
        .display_hsync(display_hsync),
        .display_vsync(display_vsync),
        .display_rgb(display_rgb),



        // ROM LOADING LINES
        // inputs
        .rom_loader_load(rom_loader_load),
        .rom_loader_sck(rom_loader_sck),
        .rom_loader_data(rom_loader_data),
        // outputs
        .rom_loader_ack(rom_loader_ack),
        

        // Keyboard
        .keycode(keycode),

        // GPIO
        .gpio_i(gpio_i),
		.gpio_o(gpio_o)


    );




endmodule 
`default_nettype wire
