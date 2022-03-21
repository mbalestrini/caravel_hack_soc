`default_nettype none
`timescale 1ns/10ps

// Mienstras no esta leyendo la linea puede escribir. deberia cortas a tiempos para empezar antes que se necesite el primer dato

module spi_video_ram_2 #(
    parameter WORD_WIDTH = 0,
    parameter VRAM_ADDRESS_WIDTH = 0,
    parameter SRAM_ADDRESS_WIDTH = 0,
    parameter HACK_SCREEN_WIDTH = 0,
    parameter HACK_SCREEN_HEIGHT = 0,
    parameter HACK_SCREEN_H_OFFSET = 0,
    parameter HACK_SCREEN_V_OFFSET = 0
)(
    input wire clk,
	input wire reset, 	


    output reg initialized, 

    
    // VIDEO VRAM READ
    input signed [9:0] clks_before_active,
    input display_active,
    input [9:0] display_hpos,
    input [9:0] display_vpos,
	output  pixel_out,


    // HACK VRAM WRITE
    input hack_clk_rise_edge,
    input [WORD_WIDTH-1:0] hack_outM,
    input [VRAM_ADDRESS_WIDTH-1:0] hack_addressM,
    input hack_writeM,


    // Serial SRAM nets 
	output reg sram_cs_n,
	output reg sram_sck,

	output reg sram_sio_oe, // output enable the SIO lines
	// SIO as inputs from SRAM	
	input wire sram_sio0_i, // sram_si_sio0 
	input wire sram_sio1_i, // sram_so_sio1
	input wire sram_sio2_i, // sram_sio2
	input wire sram_sio3_i, // sram_hold_n_sio3
	// SIO as outputs to SRAM
	output reg sram_sio0_o, // sram_si_sio0
	output reg sram_sio1_o, // sram_so_sio1
	output reg sram_sio2_o, // sram_sio2
	output reg sram_sio3_o // sram_hold_n_sio3

);

// 23LC1024 Instruction codes
`define INS_READ      8'b0000_0011                          // Read instruction
`define INS_WRMR      8'b0000_0001                          // Write Mode Register instruction
`define INS_WRITE     8'b0000_0010                          // Write instruction
`define INS_RDMR      8'b0000_0101                          // Read Mode Register instruction
`define INS_EDIO      8'b0011_1011                          // Enter Dual I/O instruction
`define INS_EQIO      8'b0011_1000                          // Enter Quad I/O instruction
`define INS_RSTIO     8'b1111_1111                          // Reset Dual and Quad I/O instruction

`define BYTEMODE  2'b00                                 // Byte operation mode
`define PAGEMODE  2'b10                                 // Page operation mode
`define SEQMODE   2'b01                                 // Sequential operation mode

`define SPIMODE   2'b00                                 // SPI I/O mode
`define SDIMODE   2'b01                                 // SDI I/O mode
`define SQIMODE   2'b10                                 // SQI I/O mode 


// 23LC1024 Address width
localparam signed CLKS_BEFORE_TRIGGER = 46; //42;  // 26? if we use the fast version of the read instruction  
// localparam SRAM_ADDRESS_WIDTH = 24;
localparam OUTPUT_BUFFER_WIDTH = SRAM_ADDRESS_WIDTH;
localparam INPUT_BUFFER_WIDTH = 4;
localparam SRAM_INSTRUCTION_WIDTH = 8;
localparam BITS_PER_CLK = 4;
`ifndef FORMAL
localparam INPUT_NIBBLES_PER_LINE = (HACK_SCREEN_WIDTH>>2);
`else
localparam INPUT_NIBBLES_PER_LINE = 3;
`endif


localparam QSI_INSTRUCTION_CLKS = 2;
localparam QSI_ADDRESS_CLKS = 6;
localparam QSI_READ_DUMMY_CLKS = 2;
localparam QSI_READ_LINE_CLKS = INPUT_NIBBLES_PER_LINE;
localparam QSI_WRITE_WORD_CLKS = WORD_WIDTH>>2;
localparam READ_LINE_TOTAL_CLKS = QSI_INSTRUCTION_CLKS + QSI_ADDRESS_CLKS + QSI_READ_DUMMY_CLKS + QSI_READ_LINE_CLKS + 1;
localparam WRITE_WORD_TOTAL_CLKS = QSI_INSTRUCTION_CLKS + QSI_ADDRESS_CLKS + QSI_WRITE_WORD_CLKS;


// states
localparam [2:0]
	state_reset 		= 3'b000,
	state_set_SQI_mode 	= 3'b001,
    state_idle 			= 3'b010,
    state_read			= 3'b011,
    state_write         = 3'b100
	
	;


wire fifo_empty;
wire fifo_full;

reg fifo_read_request;
wire [VRAM_ADDRESS_WIDTH-1:0] fifo_out_address;
wire [WORD_WIDTH-1:0] fifo_out_data;

reg fifo_write_request;
reg [VRAM_ADDRESS_WIDTH-1:0] fifo_in_address;
reg [WORD_WIDTH-1:0] fifo_in_data;

vram_write_fifo #(.DATA_WIDTH(16), .ADDRESS_WIDTH(16)) 
    write_fifo (
        .clk(clk), 
        .reset(reset),

        .read_request(fifo_read_request),
        .read_address(fifo_out_address),
        .read_data(fifo_out_data),

        .write_request(fifo_write_request),
        .write_address(fifo_in_address),
        .write_data(fifo_in_data),

        // .items_count(),
        .full(fifo_full),
        .empty(fifo_empty)
        // .overrun(),
        // .underrun()
);




wire busy;

reg [2:0] current_state;
reg [$clog2(READ_LINE_TOTAL_CLKS*4):0] state_counter;
wire [1:0] transfer_mode;
reg [$clog2(READ_LINE_TOTAL_CLKS):0] state_sram_clk_counter;
reg sram_sck_rise_edge;
reg sram_sck_fall_edge;


reg [OUTPUT_BUFFER_WIDTH-1:0] output_buffer;
reg [$clog2(OUTPUT_BUFFER_WIDTH):0] buffer_index;

reg start_read;




wire is_active_hack_line = ( display_vpos >= HACK_SCREEN_V_OFFSET ) && (display_vpos< (HACK_SCREEN_V_OFFSET+HACK_SCREEN_HEIGHT));
wire is_active_hack_col = (display_hpos >= HACK_SCREEN_H_OFFSET) && (display_hpos < (HACK_SCREEN_H_OFFSET+HACK_SCREEN_WIDTH));
// wire display_trigger_read = is_active_hack_line && (clks_before_active==CLKS_BEFORE_TRIGGER);
wire display_trigger_read = initialized && is_active_hack_line && (clks_before_active==(CLKS_BEFORE_TRIGGER-HACK_SCREEN_H_OFFSET));

// wire write_to_sram_ready = !busy && !fifo_empty && ($signed(clks_before_active)>$signed(CLKS_BEFORE_TRIGGER-HACK_SCREEN_H_OFFSET+24) );
wire write_to_sram_ready = !busy && !fifo_empty ;

wire [SRAM_ADDRESS_WIDTH-1:0] line_read_address = {display_vpos-HACK_SCREEN_V_OFFSET, 6'b0};
wire [1:0] temp_pixel_index = ~(display_hpos[1:0]);
// Squares background:
// wire background = display_vpos[3] || display_hpos[3]
// Frame background:
// wire background =   (
//                     (display_vpos==(HACK_SCREEN_V_OFFSET-1) & display_hpos[0]) || 
//                     (display_vpos==(HACK_SCREEN_HEIGHT+HACK_SCREEN_V_OFFSET) & ~display_hpos[0]) || 
//                     (display_hpos==(HACK_SCREEN_H_OFFSET-1) & display_vpos[0]) || 
//                     (display_hpos==(HACK_SCREEN_H_OFFSET+HACK_SCREEN_WIDTH) & ~display_vpos[0])
//                     );
wire background = 0;

assign pixel_out = display_active ? 
                (is_active_hack_line & is_active_hack_col) ? ~read_value[temp_pixel_index] : background
                : 0;


assign busy = (current_state!=state_idle);
assign transfer_mode = current_state==state_set_SQI_mode ? `SPIMODE : `SQIMODE;




// ** current_state && state_counter && initialized ** //
always @(posedge clk ) begin
    if(reset) begin
        current_state <= state_reset;
        state_counter <= 0;
        initialized <= 0;
    end else begin
        state_counter <= state_counter + 1'b1;        
        case (current_state)
            state_reset: begin
                if(state_counter!=0 && state_sram_clk_counter == 2) begin
                    current_state <= state_idle;
                    state_counter <= 0;
                end
            end

            state_set_SQI_mode: begin                
                if(state_sram_clk_counter == 8) begin
                    current_state <= state_idle;
                    state_counter <= 0;
                    initialized <= 1'b1;
                end
            end

            state_idle: begin
                if(!initialized) begin
                    current_state <= state_set_SQI_mode;
                    state_counter <= 0;
                end else if(fifo_empty & start_read) begin
                // end else if(start_read) begin
                    current_state <= state_read;
                    state_counter <= 0;

                end else if(write_to_sram_ready) begin
                    current_state <= state_write;
                    state_counter <= 0;
                end
            end

            state_read: begin
                // Finish reading?
                if(state_sram_clk_counter==READ_LINE_TOTAL_CLKS) begin
                    current_state <= state_idle;
                    state_counter <= 0;
                end
            end

            state_write: begin
                // Finish writing?
                if(state_sram_clk_counter==WRITE_WORD_TOTAL_CLKS) begin
                    current_state <= state_idle;
                    state_counter <= 0;
                end
            end

            default: begin
                current_state <= current_state;
            end
        endcase
    end    
end


// ** sram_sio0_o, sram_sio1_o, sram_sio2_o, sram_sio3_o ** //
always @(output_buffer or buffer_index) begin
    if(transfer_mode==`SQIMODE) begin
        sram_sio3_o = output_buffer[buffer_index];
        sram_sio2_o = output_buffer[buffer_index-1];
        sram_sio1_o = output_buffer[buffer_index-2];
        sram_sio0_o = output_buffer[buffer_index-3];
    end else begin
        sram_sio3_o = 1'b1;  // <<< HOLD_N = 1
        sram_sio2_o = 1'b0; 
        sram_sio1_o = 1'b0;
        sram_sio0_o = output_buffer[buffer_index];
    end
end

// ** start_read ** //
always @(posedge clk ) begin
    if(reset) begin
        start_read <= 0;
    end else begin
        if(!busy) begin
            start_read <= display_trigger_read;
        end
    end
end


// ** fifo_read_request ** //
always @(posedge clk) begin
    fifo_read_request <= 0;
    if(current_state==state_idle && write_to_sram_ready) begin
       fifo_read_request <= 1; 
    end    
end



// ** fifo_write_request, fifo_in_data, fifo_in_address ** //
always @(posedge clk) begin
    fifo_write_request <= 0;
    if(hack_clk_rise_edge && hack_writeM && !fifo_full) begin
        fifo_in_data <= hack_outM;
        fifo_in_address <= hack_addressM;
        fifo_write_request <= 1; 
    end    
end



// ** sram_sio_oe ** //
always @(posedge clk ) begin
    sram_sio_oe <= 1;

    if(current_state==state_read) begin
        if(state_sram_clk_counter>=10) begin
            sram_sio_oe <= 0;
        end
    end
end

// ** output_buffer && sio ** //
always @(posedge clk ) begin
    if(reset) begin
        // Keep HOLD_N high during initialization
        // sio <= 4'b1111;
    end else begin

        if(sram_sck_rise_edge) begin
            if(transfer_mode==`SQIMODE) begin                
                buffer_index <= buffer_index - 4;
            end else begin                
                buffer_index <= buffer_index - 1;
            end
        end    

        /* verilator lint_off CASEINCOMPLETE */
        case (current_state)
            state_reset: begin
                if(state_sram_clk_counter==0) begin
                    output_buffer <= {`INS_RSTIO, {(OUTPUT_BUFFER_WIDTH-SRAM_INSTRUCTION_WIDTH){1'b0}}};    
                    buffer_index <= OUTPUT_BUFFER_WIDTH-1;
               end
            end
            
            state_set_SQI_mode: begin
                if(state_sram_clk_counter==0) begin
                    output_buffer <= {`INS_EQIO, {(OUTPUT_BUFFER_WIDTH-SRAM_INSTRUCTION_WIDTH){1'b0}}};                     
                    buffer_index <= OUTPUT_BUFFER_WIDTH-1;
               end
            end
            
            state_read: begin
                if(state_sram_clk_counter==0) begin
                    // instruction
                    output_buffer <= {`INS_READ, {(OUTPUT_BUFFER_WIDTH-SRAM_INSTRUCTION_WIDTH){1'b0}}};
                    buffer_index <= OUTPUT_BUFFER_WIDTH-1;
                end else if(state_sram_clk_counter==2) begin
                    // address
                    output_buffer <= { line_read_address , {(OUTPUT_BUFFER_WIDTH-SRAM_ADDRESS_WIDTH){1'b0}}};                    
                    buffer_index <= OUTPUT_BUFFER_WIDTH-1;
               end
            end

            state_write: begin
                if(state_sram_clk_counter==0) begin
                    // instruction
                    output_buffer <= {`INS_WRITE, {(OUTPUT_BUFFER_WIDTH-SRAM_INSTRUCTION_WIDTH){1'b0}}};
                    buffer_index <= OUTPUT_BUFFER_WIDTH-1;
                end else if(state_sram_clk_counter==QSI_INSTRUCTION_CLKS) begin
                    // address
                    // As we read 2 bytes for every HACK memory address, we multiply by 2 before sending it to the 23LC1024
                    output_buffer <= { {(OUTPUT_BUFFER_WIDTH-VRAM_ADDRESS_WIDTH-1){1'b0}}, fifo_out_address , 1'b0};              
                    buffer_index <= OUTPUT_BUFFER_WIDTH-1;
                end else if(state_sram_clk_counter==(QSI_INSTRUCTION_CLKS + QSI_ADDRESS_CLKS)) begin
                    // data
                    // output_buffer <= { fifo_out_data,  {(OUTPUT_BUFFER_WIDTH-WORD_WIDTH){1'b0}}};
                    
                    // Temporal solution to invert the data word for screen, so we can read it in order while filling the screen (because HACK expects the first pixel to be on data[0] instead of data[15])
                    output_buffer <= { 
                        fifo_out_data[0], fifo_out_data[1], fifo_out_data[2], fifo_out_data[3], fifo_out_data[4], fifo_out_data[5], fifo_out_data[6], fifo_out_data[7], 
                        fifo_out_data[8], fifo_out_data[9], fifo_out_data[10], fifo_out_data[11], fifo_out_data[12], fifo_out_data[13], fifo_out_data[14], fifo_out_data[15],
                        {(OUTPUT_BUFFER_WIDTH-WORD_WIDTH){1'b0}}};

                    buffer_index <= OUTPUT_BUFFER_WIDTH-1;
                end
            end

        endcase

        /* verilator lint_on CASEINCOMPLETE */

    end
end


reg [INPUT_BUFFER_WIDTH-1:0] read_value;
// ** input_buffer ** //
always @(posedge clk ) begin
    if(current_state==state_read) begin
        if(state_sram_clk_counter>=10 && sram_sck_fall_edge) begin
            read_value <= {sram_sio3_i, sram_sio2_i, sram_sio1_i, sram_sio0_i};
        end
    end
end


// ** sram_cs_n ** //
always @(posedge clk) begin
    if(reset) begin
         sram_cs_n <= 1'b1;
    end else begin
       if(current_state!=state_idle) begin
           sram_cs_n <= 1'b0;
        end else begin
           sram_cs_n <= 1'b1;
       end
    end    
end





// ** sram_sck , state_sram_clk_counter, sram_sck_rise_edge, sram_sck_fall_edge ** //
always @(negedge clk) begin

    if(sram_cs_n) begin
        sram_sck <= 0;
        state_sram_clk_counter <= 0;
        sram_sck_rise_edge <= 0;
        sram_sck_fall_edge <= 0;
    end else begin
        sram_sck_rise_edge <= 0;
        sram_sck_fall_edge <= 0;

        if(current_state==state_idle) begin
            sram_sck <= 0;
            state_sram_clk_counter <= 0;
        // end else if(current_state!=state_read || state_sram_clk_counter < 9) begin
        end else if(current_state!=state_read) begin
            sram_sck <= state_counter[0];
            sram_sck_fall_edge <= sram_sck && ~state_counter[0];
            if(~sram_sck && state_counter[0]) begin
                state_sram_clk_counter <= state_sram_clk_counter + 1;
                sram_sck_rise_edge <= 1;               
            end
        end else begin
            sram_sck <= state_counter[0] ^ state_counter[1] ;
            sram_sck_fall_edge <= sram_sck && ~(state_counter[0] ^ state_counter[1]);
            if(~sram_sck && (state_counter[0] ^ state_counter[1])) begin
                state_sram_clk_counter <= state_sram_clk_counter + 1;
                sram_sck_rise_edge <= 1;
            end
        end
    end

end







`ifdef FORMAL

    localparam READ_TRIGGER_BEFORE_ACTIVE_CLKS = 26;

    /*
    //Full 640x480 data
    localparam ACTIVE_LINES = 480;
    localparam VA_END  = ACTIVE_LINES;
    localparam HCOUNT_MAX = 800;
    localparam VCOUNT_MAX = 525;
    localparam HA_STA = 160;    
    
    /*/

    // Smaller values for testing
    localparam ACTIVE_LINES = 2;
    localparam VA_END  = ACTIVE_LINES;
    localparam HCOUNT_MAX = 20;
    localparam VCOUNT_MAX = 3;
    localparam HA_STA = 12;
    //*/ 

    
    reg f_past_valid = 0;
    reg initial_reset_passed = 0;


    reg [9:0] h_count;
    reg [9:0] v_count;
    reg [3:0] some_input_data = 'b1010;


    initial begin
        assume(reset);        
        assume(!initialized);
        // assume(line_read_address==display_vpos*'h40);
        // assume(display_trigger_read==0);
        // assume(current_state==state_set_SQI_mode);
        // assume(line_read_address=='h40);
        // assume(h_count == 150);
    end

    // The clock toggles.
    reg last_clk = 1'b0;
    always @($global_clock) begin
        assume (clk == !last_clk);
        last_clk <= clk;
        
    end
    
    always @(negedge clk) begin
        if(f_past_valid) begin
            // if(reset) begin
            //     assume($past(reset));
            // end
            if(initial_reset_passed) begin
                assume(reset==0);
            end
        end
    end

    always @(posedge clk) begin 


        if(~((h_count < HA_STA) | (v_count > ACTIVE_LINES - 1))) begin
            assume(display_active);    
        end else begin
            assume(display_active==0);
        end
        
        
        if((h_count+READ_TRIGGER_BEFORE_ACTIVE_CLKS == HA_STA) && (v_count <= ACTIVE_LINES - 1)) begin            
        // if(~(( (h_count+10) == 160) | (v_count > 480 - 1))) begin
            assume(display_trigger_read)   ;
        end else begin
            assume(display_trigger_read==0)   ;
        end

    
        f_past_valid <= 1;



        // if((h_count+READ_TRIGGER_BEFORE_ACTIVE_CLKS == HA_STA) && (v_count <= ACTIVE_LINES - 1)) begin            
        // // if(~(( (h_count+10) == 160) | (v_count > 480 - 1))) begin
        //     assume(display_trigger_read)   ;
        // end else begin
        //     assume(display_trigger_read==0)   ;
        // end


        if(f_past_valid) begin            
            if($fell(reset)) begin
                initial_reset_passed <= 1;
            end

            if(initial_reset_passed) begin
                COVER_STATE_IDLE: cover(current_state==state_idle);

                COVER_STATE_READ: cover(current_state==state_read);

                COVER_FINISH_READ: cover($past(current_state)==state_read && current_state==state_idle);

            end

        end        
        

    end

`endif

endmodule