`default_nettype none
`timescale 1ns/10ps

module hack_cpu #(
		parameter WORD_WIDTH = 16,
		parameter INSTRUCTION_WIDTH = WORD_WIDTH,
		parameter RAM_ADDRESS_WIDTH = $clog2(32768),
		parameter ROM_ADDRESS_WIDTH = $clog2(32768)
	)(
		input clk, 
		input [WORD_WIDTH-1:0] inM, 
		input [INSTRUCTION_WIDTH-1:0] instruction, 
		input reset,
		output [WORD_WIDTH-1:0] outM, 
		output writeM, 
		output [RAM_ADDRESS_WIDTH-1:0] addressM, 
		output [ROM_ADDRESS_WIDTH-1:0] pc
		);

	
	// A REG
	wire [WORD_WIDTH-1:0] areg_in;
	wire areg_load;
	wire [WORD_WIDTH-1:0] areg_out;
	register #(.D_WIDTH(WORD_WIDTH)) AReg (.clk(clk), .in(areg_in), .load(areg_load), .out(areg_out));
	
	// D REG
	wire [WORD_WIDTH-1:0] dreg_in;
	wire dreg_load;
	wire [WORD_WIDTH-1:0] dreg_out;
	register #(.D_WIDTH(WORD_WIDTH)) DReg (.clk(clk), .in(dreg_in), .load(dreg_load), .out(dreg_out));
	
	// Program Counter
	// Por ahora hago esto para manejar la diferencia de tamaños entre PC.out y hack_cpu.pc
	wire pc_load;
	wire pc_inc;
	wire [WORD_WIDTH-1:0] pc_in;
	
	// Hasta que solucione la diferencia de tamanos deshabilito el warning de UNUSED causado por el pc_output[15]
	/* verilator lint_off UNUSED */
	wire [WORD_WIDTH-1:0] pc_output;
	/* verilator lint_off UNUSED */
	
	pc #(.D_WIDTH(WORD_WIDTH)) PC (.clk(clk), .reset(reset), .in(pc_in), .load(pc_load), .inc(pc_inc), .out(pc_output));
	
	// ALU
	wire [WORD_WIDTH-1:0] alu_x;
	wire [WORD_WIDTH-1:0] alu_y;
	wire alu_zx, alu_nx, alu_zy, alu_ny, alu_f, alu_no;
	wire [WORD_WIDTH-1:0] alu_out;
	wire alu_zr, alu_ng;
	hack_alu #(.D_WIDTH(WORD_WIDTH)) ALU (	.x(alu_x), .y(alu_y), .zx(alu_zx), .nx(alu_nx), .zy(alu_zy), .ny(alu_ny), .f(alu_f), .no(alu_no), 
											.out(alu_out), .zr(alu_zr), .ng(alu_ng));
				
	
	
	wire instruction_type_A;
	wire [RAM_ADDRESS_WIDTH-1:0] instruction_A_address;	
	wire instruction_type_C;	
	wire instruction_C_dest_a;
	wire instruction_C_dest_d;	
	wire instruction_C_dest_m;		
	wire instruction_C_source_m;	

	/* verilator lint_off UNUSED */
	wire instruction_C_noJump;
	/* verilator lint_on UNUSED */
	wire instruction_C_jgt;
	wire instruction_C_jeq;
	wire instruction_C_jge;
	wire instruction_C_jlt;
	wire instruction_C_jne;
	wire instruction_C_jle;
	wire instruction_C_jmp;

	assign instruction_type_A = (instruction[INSTRUCTION_WIDTH-1]==0 ? 1'b1 : 1'b0);
	assign instruction_type_C = (instruction[INSTRUCTION_WIDTH-1]==1 ? 1'b1 : 1'b0);
	assign instruction_A_address = instruction[INSTRUCTION_WIDTH-2:0];
	
	assign instruction_C_source_m = instruction[12];
	assign alu_zx=instruction[11];
	assign alu_nx=instruction[10];
	assign alu_zy=instruction[9];
	assign alu_ny=instruction[8];
	assign alu_f=instruction[7];
	assign alu_no=instruction[6];
	assign instruction_C_dest_a = instruction[5];
	assign instruction_C_dest_d = instruction[4];
	assign instruction_C_dest_m = instruction[3];
	
	dmux8way #(.D_WIDTH(1)) DMuxJMP(.in(1'b1), .sel(instruction[2:0]), 
					.a(instruction_C_noJump), 
					.b(instruction_C_jgt),
					.c(instruction_C_jeq),
					.d(instruction_C_jge),
					.e(instruction_C_jlt),
					.f(instruction_C_jne),
					.g(instruction_C_jle),
					.h(instruction_C_jmp)
					);
						
	// A REG
	assign areg_load = instruction_type_A | (instruction_type_C & instruction_C_dest_a);
	assign areg_in = instruction_type_A ? {1'b0,instruction_A_address} : alu_out;

	
	// D REG
	assign dreg_load = instruction_type_C & instruction_C_dest_d;
	assign dreg_in = alu_out;
	
	// outM , assignM , writeM
	assign outM = alu_out;
    assign addressM = areg_out[RAM_ADDRESS_WIDTH-1:0];
    // Opcion para intentar usar el mismo clock para las memorias que para el CPU. El problema es que se arma un loop 	
	//assign addressM = areg_load ? areg_in : areg_out[RAM_ADDRESS_WIDTH-1:0];
	
	
	assign writeM = instruction_type_C & instruction_C_dest_m;
	
	// ALU
	assign alu_x = dreg_out;
	assign alu_y = instruction_C_source_m ? inM : areg_out;
	
	
	// PC REG
	wire jump_condition_met = 	  (instruction_C_jgt & ~(alu_zr | alu_ng)) 
								| (instruction_C_jeq & alu_zr) 
								| (instruction_C_jge & (alu_zr | ~alu_ng)) 
								| (instruction_C_jlt & alu_ng)
								| (instruction_C_jne & ~alu_zr)
								| (instruction_C_jle & (alu_zr | alu_ng))
								| (instruction_C_jmp)
								;

	assign pc_load = instruction_type_C & jump_condition_met;
	assign pc_inc = ~pc_load;
	//assign pc_in = areg_out;
	// This change allows to assign to A and jump to that value on the same cycle:
	// @somePointerToRom 
	// A=M;JMP 
	assign pc_in = areg_load ? areg_in : areg_out;

	// PC address out
	//assign pc = pc_load ? pc_in : pc_output[ROM_ADDRESS_WIDTH-1:0];
	assign pc = pc_output[ROM_ADDRESS_WIDTH-1:0];
	


	`ifdef verilator
   	function [ROM_ADDRESS_WIDTH-1:0] get_pc;
		// verilator public
      	get_pc = pc;
   	endfunction // 

	function [WORD_WIDTH-1:0] get_dreg;
		// verilator public
      	get_dreg = dreg_out;
   	endfunction // 

	
	`endif


endmodule
