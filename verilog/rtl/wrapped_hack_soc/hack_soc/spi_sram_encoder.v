`default_nettype none
`timescale 1ns/10ps

module spi_sram_encoder #(
	parameter WORD_WIDTH = 16,
	parameter ADDRESS_WIDTH = 16
) (
	input wire clk,
	input wire reset, 	

	input wire request,
	output wire busy,
	output reg initialized,

	// Parallel memory nets 
	input wire [ADDRESS_WIDTH-1:0] address,
	input wire write_enable,
	output reg [WORD_WIDTH-1:0] data_in,
	input wire [WORD_WIDTH-1:0] data_out,


	// Serial SRAM nets 
	output reg sram_cs_n,
	output sram_sck,

	output reg sram_sio_oe, // output enable the SIO lines
	// SIO as inputs from SRAM	
	input wire sram_sio0_i, // sram_si_sio0 
	input wire sram_sio1_i, // sram_so_sio1
	input wire sram_sio2_i, // sram_sio2
	input wire sram_sio3_i, // sram_hold_n_sio3
	// SIO as outputs to SRAM
	output wire sram_sio0_o, // sram_si_sio0
	output wire sram_sio1_o, // sram_so_sio1
	output wire sram_sio2_o, // sram_sio2
	output wire sram_sio3_o // sram_hold_n_sio3
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


function [31:0] max3(input [31:0] x, y, z);
    begin
        max3 = x > y ? (x > z ? x :z) : (y > z ? y : z);
    end
endfunction

// 23LC1024 Address width
localparam SRAM_ADDRESS_WIDTH = 24;
localparam SRAM_INSTRUCTION_WIDTH = 8;
localparam OUTPUT_BUFFER_WIDTH = max3(SRAM_ADDRESS_WIDTH, SRAM_INSTRUCTION_WIDTH ,WORD_WIDTH);// 24;
localparam INPUT_BUFFER_WIDTH = WORD_WIDTH;
localparam INPUT_DUMMY_WIDTH = 8;
localparam BITS_PER_CLK = 4;

// states
localparam [2:0]
	state_idle 			= 3'b000,
	state_start			= 3'b001,
	state_instruction 	= 3'b010,
	state_address 		= 3'b011,
	state_read 			= 3'b100,
	state_write 		= 3'b101,	
	state_reset 		= 3'b110,
	state_set_SQI_mode 	= 3'b111
	;

reg [2:0] current_state;
reg [4:0] initializing_step;


reg [ADDRESS_WIDTH-1:0] request_address;
reg [WORD_WIDTH-1:0] request_data_out;
reg request_write;

reg [OUTPUT_BUFFER_WIDTH-1:0] output_buffer;
reg [$clog2(OUTPUT_BUFFER_WIDTH)-1:0] output_bits_left;

reg [INPUT_BUFFER_WIDTH-1:0] input_buffer;
reg [$clog2(INPUT_BUFFER_WIDTH + INPUT_DUMMY_WIDTH)-1:0] input_bits_left;


reg toggled_sram_sck;

assign sram_sck = ~sram_cs_n & toggled_sram_sck;

// aliases
// wire sio0 = sram_si_sio0;
// wire sio1 = sram_so_sio1;
// wire sio2 = sram_sio2;
// wire sio3 = sram_hold_n_sio3;
// wire [3:0] sio_o;
wire [3:0] sio_i = {sram_sio3_i, sram_sio2_i, sram_sio1_i, sram_sio0_i};
wire [3:0] sio_o = output_buffer[OUTPUT_BUFFER_WIDTH-1:OUTPUT_BUFFER_WIDTH-4];
// assign sio_o = next_output_data;



assign {sram_sio3_o, sram_sio2_o, sram_sio1_o, sram_sio0_o} = sio_o;

assign busy = (current_state!=state_idle);





always @(posedge clk) begin
	
	

	if (reset) begin
		// reset
		current_state <= state_reset;		

		initialized <= 1'b0;
		sram_cs_n <= 1'b1;				
		sram_sio_oe <= 1'b1;
		initializing_step <= 0;

		// set output to 1 to keep HOLD_N high during initialization
		output_buffer[OUTPUT_BUFFER_WIDTH-1:OUTPUT_BUFFER_WIDTH-4] <= 4'b1111;
		
		input_buffer <= 0;
		data_in <= 0;

		toggled_sram_sck <= 0;
	end else begin
	
		toggled_sram_sck <= ~toggled_sram_sck;

		// Active transfer states, hapenning at the falling edge sram_clk	
		if(toggled_sram_sck==1'b1) begin
			/* verilator lint_off CASEINCOMPLETE */
			case (current_state) 

				state_reset:
					begin
						if(sram_cs_n==1'b1) 
							sram_cs_n <= 1'b0;								
						
						initializing_step <= initializing_step + 1;

						// Send reset instruction
						case (initializing_step)
							0: output_buffer <= {`INS_RSTIO, {(OUTPUT_BUFFER_WIDTH-SRAM_INSTRUCTION_WIDTH){1'b0}}};
							1: output_buffer <= output_buffer << BITS_PER_CLK;
							default: 
								begin
									current_state <= state_set_SQI_mode;
									sram_cs_n <= 1'b1;
									initializing_step <= 0;
								end

						endcase

					end
				
				state_set_SQI_mode:
					begin
						// Enable device
						if(sram_cs_n==1'b1)
							sram_cs_n <= 1'b0;		
						
						initializing_step <= initializing_step + 1;

						// Output INS_EQIO (8'b0011_1000): Enter Quad I/O instruction
						case (initializing_step)
							0: output_buffer[20] <= 0;
							1: output_buffer[20] <= 0;
							2: output_buffer[20] <= 1;
							3: output_buffer[20] <= 1;
							4: output_buffer[20] <= 1;
							5: output_buffer[20] <= 0;
							6: output_buffer[20] <= 0;
							7: output_buffer[20] <= 0;
							8: 	begin
									current_state <= state_idle;
									sram_cs_n <= 1'b1;	
									initialized <= 1'b1;								
								end

						endcase
					end

				state_idle:
					begin
						if(request && !busy) begin
							current_state <= state_start;

							// save request
							request_address <= address;
							request_write <= write_enable;
							request_data_out <= data_out;

							
							// Enable output GPIO
							sram_sio_oe <= 1'b1;
						end
					end
				
				state_start:					
					begin
						// Enable device
						sram_cs_n <= 1'b0;		

						current_state <= state_instruction;

						// fill the buffer with the instruction data
						if(request_write) begin
							output_buffer <= {`INS_WRITE, {(OUTPUT_BUFFER_WIDTH-SRAM_INSTRUCTION_WIDTH){1'b0}}};
							output_bits_left <= SRAM_INSTRUCTION_WIDTH;
						end else begin
							output_buffer <= {`INS_READ,  {(OUTPUT_BUFFER_WIDTH-SRAM_INSTRUCTION_WIDTH){1'b0}}};
							output_bits_left <= SRAM_INSTRUCTION_WIDTH;					
						end			
					end
				
				state_instruction:
					begin
						
						// Last bits of instruction?
						if(output_bits_left == BITS_PER_CLK) begin
							current_state <= state_address;			
							// Load Address
							// As we read 2 bytes for every HACK memory address, we multiply by 2 before sending it to the 23LC1024
							output_buffer <= { {(OUTPUT_BUFFER_WIDTH-ADDRESS_WIDTH-1){1'b0}}, request_address[ADDRESS_WIDTH-1:0] , 1'b0};
							output_bits_left <= SRAM_ADDRESS_WIDTH;
						end else begin
							// Output next bits
							output_buffer <= output_buffer << BITS_PER_CLK;
							output_bits_left <= output_bits_left - BITS_PER_CLK;							
						end					
					end
				
				state_address:
					begin
						
						// Last bits of address?
						if(output_bits_left == BITS_PER_CLK) begin
							if(request_write) begin
								current_state <= state_write;

								// Load output data
								output_buffer <= {request_data_out, {(OUTPUT_BUFFER_WIDTH-WORD_WIDTH){1'b0}}};
								output_bits_left <= WORD_WIDTH;
							end else begin
								current_state <= state_read;
								
								// Enable input GPIO
								sram_sio_oe <= 1'b0;
								input_bits_left <= INPUT_BUFFER_WIDTH + INPUT_DUMMY_WIDTH;
							end
							
						end else begin
							// Output next bits
							output_buffer <= output_buffer << BITS_PER_CLK;
							output_bits_left <= output_bits_left - BITS_PER_CLK;							
						end			
					end

				state_write:
					begin
						
						// Last bits of data?
						if(output_bits_left == BITS_PER_CLK) begin
							current_state <= state_idle;

							// On write I should also output the value we just wrote
							data_in <= request_data_out;

							// sram deselected
							sram_cs_n <= 1'b1;
							
						end else begin
							// Output next bits
							output_buffer <= output_buffer << BITS_PER_CLK;
							output_bits_left <= output_bits_left - BITS_PER_CLK;							

							
						end					
					end

				state_read:
					begin

						input_buffer <= {input_buffer[INPUT_BUFFER_WIDTH-BITS_PER_CLK-1:0] , sio_i};

						// Last bits of data?
						if(input_bits_left == BITS_PER_CLK) begin

							data_in <= {input_buffer[INPUT_BUFFER_WIDTH-BITS_PER_CLK-1:0] , sio_i};

							current_state <= state_idle;

							// sram deselected
							sram_cs_n <= 1'b1;

						end else begin
							input_bits_left <= input_bits_left - BITS_PER_CLK;
						end
					end


				
				

			endcase
			/* lint_on */
		end
	
	end
	
end





`ifdef FORMAL
    // register for knowing if we have just started
    reg f_past_valid = 0;
    // start in reset
    initial assume(reset);
    initial assume(current_state==0);

    always @(posedge clk) begin 

		assume(address==16'hAED0);

    	f_past_valid <= 1;

		// if(f_past_valid && !$past(reset) && !busy && $past(toggled_sram_sck==1)) begin
		// 	request <= 1'b1;
		// end else begin 
		// 	request <= 1'b0;
		// end

		
 		
 		if(!reset && sram_cs_n==1'b0) begin
 			ASSERT_BUSY: assert(busy);
 		end
		
		if(current_state==state_read) begin
			ASSERT_OUTPUT_DISABLED_ON_READ: assert(sram_sio_oe==0);
		end

 		if(f_past_valid) begin
 			
 			COVER_READ: cover($past(current_state)==state_read && current_state==state_idle);
 			COVER_WRITE: cover($past(current_state)==state_write && current_state==state_idle);

 			COVER_INITIALIZED: cover(initialized);

 			if(current_state!=state_reset && current_state!=state_start && current_state!=state_set_SQI_mode) begin
 				ASSERT_INITILIZED: assert(initialized);
 			end

	 		if(sram_cs_n==1'b0 && toggled_sram_sck==1'b1) begin
	 			ASSERT_SRAM_INPUT_SET_BEFORE_CLOCK: 
	 				assert($past(sio_o)==sio_o); 			
	 		end

	 		if(!$past(reset) && current_state==state_idle) begin
				ASSERT_SRAM_OFF_ON_IDLE:
					assert(sram_cs_n==1'b1);

				if(!reset && $past(current_state)==state_write) begin
					ASSERT_OUTPUT_EQUAL_INPUT_ON_WRITE: assert(data_in==request_data_out);
				end
			end

			
	 	end
 		
    end
`endif    
	
endmodule