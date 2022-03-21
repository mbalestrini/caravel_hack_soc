`default_nettype none
`timescale 1ns/10ps

// FIFO based on https://zipcpu.com/blog/2017/07/29/fifo.html

module vram_write_fifo #(
    parameter DATA_WIDTH = 16,
    parameter ADDRESS_WIDTH = 16    
)(
    input clk, 
    input reset,

    input read_request,
    output [ADDRESS_WIDTH-1:0] read_address,
    output [DATA_WIDTH-1:0] read_data,

    input write_request,
    input [ADDRESS_WIDTH-1:0] write_address,
    input [DATA_WIDTH-1:0] write_data,

    output reg [FIFO_INDEX_WIDTH-1:0] items_count,
    output wire full,
    output wire empty,
    output reg overrun,
    output reg underrun
);

localparam FIFO_INDEX_WIDTH = 5; // 2^5 => 32. Total FIFO Memory 32x32 bits

// reg [(DATA_WIDTH + ADDRESS_WIDTH)-1:0] fifo_mem [0:(1<<FIFO_INDEX_WIDTH)-1];
reg [FIFO_INDEX_WIDTH-1:0] write_pointer;
reg [FIFO_INDEX_WIDTH-1:0] read_pointer;
wire [FIFO_INDEX_WIDTH-1:0] next_pointer;


assign	next_pointer = write_pointer + 1'b1;
assign	full  = (next_pointer == read_pointer);
assign	empty = (write_pointer  == read_pointer);


// ** write_pointer ** //
always @(posedge clk ) begin
    if(reset) begin
        write_pointer <= 0;
        overrun <= 0;
    end else if(write_request) begin
        if ((!full) || (read_request)) begin
			write_pointer <= (write_pointer + 1'b1);
        end else begin
			overrun <= 1'b1;
        end
    end
end

// ** read pointer ** //
always @(posedge clk ) begin
    if(reset) begin
        read_pointer <= 0;
        underrun <= 0;
    end else if(read_request) begin
        if(!empty) begin
            read_pointer <= (read_pointer + 1'b1);
        end else begin
            underrun <= 1'b1;
        end
    end
end


wire [(DATA_WIDTH + ADDRESS_WIDTH)-1:0] dffrf_DA;

DFFRF_2R1W dffrf(
    .CLK(clk),
    .DA(dffrf_DA),
    // .DB(),
    .DW( {write_address, write_data} ),

    .RA(read_pointer),
    .RB(5'b0),
    .RW(write_pointer),

    .WE(1'b1)
);





// ** read_address & read_data ** //
//always @(posedge clk ) begin
assign {read_address, read_data} = dffrf_DA;    
// assign {read_address, read_data} = fifo_mem[read_pointer];    
//end

// ** fifo_mem ** //
// always @(posedge clk ) begin
    // fifo_mem[write_pointer] <= {write_address, write_data};    
// end


// ** items_count ** //
always @(posedge clk ) begin
    if (reset)	begin
		items_count <= 0;
    end else begin
        casez({ write_request, read_request, !full, !empty }) 
	        4'b01?1: items_count <= items_count - 1'b1;	// A successful read
	        4'b101?: items_count <= items_count + 1'b1;	// A successful write
	        4'b1110: items_count <= items_count + 1'b1;	// Successful write, failed read
	        // 4'b11?1: Successful read *and* write -- no change
	        default: items_count <= items_count;	// Default, no change
	    endcase
    end
end





`ifdef FORMAL
    // register for knowing if we have just started
    reg f_past_valid = 0;
    reg initial_reset_passed = 0;

    initial assume(reset);

    always @(posedge clk) begin 

    	f_past_valid <= 1;

        
                

        if(f_past_valid) begin
            if($fell(reset)) begin
    			initial_reset_passed <= 1;
		    end

            // if(!$past(reset) && items_count==0) begin
            //         assert(empty);
            // end
                
            if(initial_reset_passed) begin
                COVER_FULL: cover(full);
                
                COVER_OVERRUN: cover(overrun);
                COVER_UNDERRUN: cover(underrun);
                
                if(!$past(reset) && $past(read_request) && $past(!empty)) begin
                    ASSERT_READ_POINTER_ADVACE: assert(read_pointer== {$past(read_pointer)}+ {{FIFO_INDEX_WIDTH-1{1'b0}}, 1'b1}  );
                end

               
            
            end

        end

        
    end


`endif



endmodule
