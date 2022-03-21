	read_liberty /home/videogamo/Work/mpw5/pdk/sky130A/libs.ref/sky130_fd_sc_hd/lib/sky130_fd_sc_hd__tt_025C_1v80.lib;
	read_liberty /home/videogamo/Work/mpw5/pdk/sky130A/libs.ref/sky130_sram_macros/lib/sky130_sram_2kbyte_1rw1r_32x512_8_TT_1p8V_25C.lib
	read_liberty /home/videogamo/Work/mpw5/pdk/sky130A/libs.ref/sky130_fd_sc_hvl/lib/sky130_fd_sc_hvl__tt_025C_3v30.lib;
	read_liberty /home/videogamo/Work/mpw5/pdk/sky130A/libs.ref/sky130_fd_sc_hvl/lib/sky130_fd_sc_hvl__tt_025C_3v30_lv1v80.lib;
	read_liberty /home/videogamo/Work/mpw5/pdk/sky130A/libs.ref/sky130_fd_io/lib/sky130_fd_io__top_gpiov2_tt_tt_025C_1v80_3v30.lib;
	read_liberty /home/videogamo/Work/mpw5/pdk/sky130A/libs.ref/sky130_fd_io/lib/sky130_fd_io__top_ground_hvc_wpad_tt_025C_1v80_3v30_3v30.lib;
	read_liberty /home/videogamo/Work/mpw5/pdk/sky130A/libs.ref/sky130_fd_io/lib/sky130_fd_io__top_ground_lvc_wpad_tt_025C_1v80_3v30.lib;
	read_liberty /home/videogamo/Work/mpw5/pdk/sky130A/libs.ref/sky130_fd_io/lib/sky130_fd_io__top_ground_lvc_wpad_tt_100C_1v80_3v30.lib;
	read_liberty /home/videogamo/Work/mpw5/pdk/sky130A/libs.ref/sky130_fd_io/lib/sky130_fd_io__top_power_lvc_wpad_tt_025C_1v80_3v30_3v30.lib;
	read_liberty /home/videogamo/Work/mpw5/pdk/sky130A/libs.ref/sky130_fd_io/lib/sky130_fd_io__top_xres4v2_tt_tt_025C_1v80_3v30.lib;
	read_liberty /home/videogamo/Work/mpw5/pdk/sky130A/libs.ref/sky130_fd_io/lib/sky130_ef_io__gpiov2_pad_tt_tt_025C_1v80_3v30.lib;
	read_liberty /home/videogamo/Work/mpw5/pdk/sky130A/libs.ref/sky130_fd_io/lib/sky130_ef_io__vccd_lvc_clamped_pad_tt_025C_1v80_3v30_3v30.lib;
	read_liberty /home/videogamo/Work/mpw5/pdk/sky130A/libs.ref/sky130_fd_io/lib/sky130_ef_io__vdda_hvc_clamped_pad_tt_025C_1v80_3v30_3v30.lib;
	read_liberty /home/videogamo/Work/mpw5/pdk/sky130A/libs.ref/sky130_fd_io/lib/sky130_ef_io__vssa_hvc_clamped_pad_tt_025C_1v80_3v30_3v30.lib;
	read_liberty /home/videogamo/Work/mpw5/pdk/sky130A/libs.ref/sky130_fd_io/lib/sky130_ef_io__vssd_lvc_clamped3_pad_tt_025C_1v80_3v30.lib;
	read_liberty /home/videogamo/Work/mpw5/pdk/sky130A/libs.ref/sky130_fd_io/lib/sky130_ef_io__vccd_lvc_clamped3_pad_tt_025C_1v80_3v30_3v30.lib;
	read_liberty /home/videogamo/Work/mpw5/pdk/sky130A/libs.ref/sky130_fd_io/lib/sky130_ef_io__vssd_lvc_clamped_pad_tt_025C_1v80_3v30.lib;
	read_verilog /home/videogamo/Work/mpw5/caravel_hack_soc/mgmt_core_wrapper/verilog/gl/mgmt_core.v;
	read_verilog /home/videogamo/Work/mpw5/caravel_hack_soc/mgmt_core_wrapper/verilog/gl/DFFRAM.v;
	read_verilog /home/videogamo/Work/mpw5/caravel_hack_soc/mgmt_core_wrapper/verilog/gl/mgmt_core_wrapper.v;
	read_verilog ./verilog/gl/caravel_clocking.v;
	read_verilog ./verilog/gl/digital_pll.v;
	read_verilog ./verilog/gl/housekeeping.v;
	read_verilog ./verilog/gl/gpio_logic_high.v;
	read_verilog ./verilog/gl/gpio_control_block.v;
	read_verilog ./verilog/gl/gpio_defaults_block.v;
	read_verilog ./verilog/gl/gpio_defaults_block_0403.v;
	read_verilog ./verilog/gl/gpio_defaults_block_1803.v;
	read_verilog ./verilog/gl/mgmt_protect_hv.v;
	read_verilog ./verilog/gl/mprj_logic_high.v;
	read_verilog ./verilog/gl/mprj2_logic_high.v;
	read_verilog ./verilog/gl/mgmt_protect.v;
	read_verilog ./verilog/gl/user_id_programming.v;
	read_verilog ./verilog/gl/xres_buf.v;
	read_verilog ./verilog/gl/spare_logic_block.v;
	read_verilog ./verilog/gl/chip_io.v;
	read_verilog ./verilog/gl/caravel.v;

		
	# begin CUSTOM section

	#read_liberty /home/videogamo/Work/mpw5/pdk/sky130A/libs.ref/sky130_sram_macros/lib/sky130_sram_1kbyte_1rw1r_32x256_8_TT_1p8V_25C.lib;

	read_verilog ../verilog/gl/DFFRF_2R1W.powered.nl.v
	read_verilog ../verilog/gl/wrapped_hack_soc_dffram.v
	read_verilog ../verilog/gl/user_project_wrapper.v 
	


	# end CUSTOM section



	link_design caravel;

	read_spef -path mprj/hack_soc/\soc.spi_video_ram_1.write_fifo.dffrf ../spef/DFFRF_2R1W.spef 
	read_spef -path mprj ../spef/user_project_wrapper.spef
	read_spef -path mprj/hack_soc ../spef/wrapped_hack_soc_dffram.spef


	read_spef -path soc/DFFRAM_0 /home/videogamo/Work/mpw5/caravel_hack_soc/mgmt_core_wrapper/spef/DFFRAM.spef;
	read_spef -path soc/core /home/videogamo/Work/mpw5/caravel_hack_soc/mgmt_core_wrapper/spef/mgmt_core.spef;
	read_spef -path soc /home/videogamo/Work/mpw5/caravel_hack_soc/mgmt_core_wrapper/spef/mgmt_core_wrapper.spef;
	read_spef -path padframe ./spef/chip_io.spef;
	read_spef -path rstb_level ./spef/xres_buf.spef;
	read_spef -path pll ./spef/digital_pll.spef;
	read_spef -path housekeeping ./spef/housekeeping.spef;
	read_spef -path mgmt_buffers/powergood_check ./spef/mgmt_protect_hv.spef;
	read_spef -path mgmt_buffers/mprj_logic_high_inst ./spef/mprj_logic_high.spef;
	read_spef -path mgmt_buffers/mprj2_logic_high_inst ./spef/mprj2_logic_high.spef;
	read_spef -path mgmt_buffers ./spef/mgmt_protect.spef;
	read_spef -path \gpio_control_bidir_1[0] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_bidir_1[1] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_bidir_2[1] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_bidir_2[2] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_in_1[0] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_in_1[10] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_in_1[1] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_in_1[2] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_in_1[3] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_in_1[4] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_in_1[5] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_in_1[6] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_in_1[7] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_in_1[8] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_in_1[9] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_in_1a[0] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_in_1a[1] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_in_1a[2] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_in_1a[3] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_in_1a[4] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_in_1a[5] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_in_2[0] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_in_2[10] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_in_2[11] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_in_2[12] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_in_2[13] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_in_2[14] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_in_2[15] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_in_2[1] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_in_2[2] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_in_2[3] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_in_2[4] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_in_2[5] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_in_2[6] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_in_2[7] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_in_2[8] ./spef/gpio_control_block.spef;
	read_spef -path \gpio_control_in_2[9] ./spef/gpio_control_block.spef;
	read_spef -path gpio_defaults_block_0 ./spef/gpio_defaults_block_1803.spef;
	read_spef -path gpio_defaults_block_1 ./spef/gpio_defaults_block_1803.spef;
	read_spef -path gpio_defaults_block_2 ./spef/gpio_defaults_block_0403.spef;
	read_spef -path gpio_defaults_block_3 ./spef/gpio_defaults_block_0403.spef;
	read_spef -path gpio_defaults_block_4 ./spef/gpio_defaults_block_0403.spef;
	read_spef -path gpio_defaults_block_5 ./spef/gpio_defaults_block.spef;
	read_spef -path gpio_defaults_block_6 ./spef/gpio_defaults_block.spef;
	read_spef -path gpio_defaults_block_7 ./spef/gpio_defaults_block.spef;
	read_spef -path gpio_defaults_block_8 ./spef/gpio_defaults_block.spef;
	read_spef -path gpio_defaults_block_9 ./spef/gpio_defaults_block.spef;
	read_spef -path gpio_defaults_block_10 ./spef/gpio_defaults_block.spef;
	read_spef -path gpio_defaults_block_11 ./spef/gpio_defaults_block.spef;
	read_spef -path gpio_defaults_block_12 ./spef/gpio_defaults_block.spef;
	read_spef -path gpio_defaults_block_13 ./spef/gpio_defaults_block.spef;
	read_spef -path gpio_defaults_block_14 ./spef/gpio_defaults_block.spef;
	read_spef -path gpio_defaults_block_15 ./spef/gpio_defaults_block.spef;
	read_spef -path gpio_defaults_block_16 ./spef/gpio_defaults_block.spef;
	read_spef -path gpio_defaults_block_17 ./spef/gpio_defaults_block.spef;
	read_spef -path gpio_defaults_block_18 ./spef/gpio_defaults_block.spef;
	read_spef -path gpio_defaults_block_19 ./spef/gpio_defaults_block.spef;
	read_spef -path gpio_defaults_block_20 ./spef/gpio_defaults_block.spef;
	read_spef -path gpio_defaults_block_21 ./spef/gpio_defaults_block.spef;
	read_spef -path gpio_defaults_block_22 ./spef/gpio_defaults_block.spef;
	read_spef -path gpio_defaults_block_23 ./spef/gpio_defaults_block.spef;
	read_spef -path gpio_defaults_block_24 ./spef/gpio_defaults_block.spef;
	read_spef -path gpio_defaults_block_25 ./spef/gpio_defaults_block.spef;
	read_spef -path gpio_defaults_block_26 ./spef/gpio_defaults_block.spef;
	read_spef -path gpio_defaults_block_27 ./spef/gpio_defaults_block.spef;
	read_spef -path gpio_defaults_block_28 ./spef/gpio_defaults_block.spef;
	read_spef -path gpio_defaults_block_29 ./spef/gpio_defaults_block.spef;
	read_spef -path gpio_defaults_block_30 ./spef/gpio_defaults_block.spef;
	read_spef -path gpio_defaults_block_31 ./spef/gpio_defaults_block.spef;
	read_spef -path gpio_defaults_block_32 ./spef/gpio_defaults_block.spef;
	read_spef -path gpio_defaults_block_33 ./spef/gpio_defaults_block.spef;
	read_spef -path gpio_defaults_block_34 ./spef/gpio_defaults_block.spef;
	read_spef -path gpio_defaults_block_35 ./spef/gpio_defaults_block.spef;
	read_spef -path gpio_defaults_block_36 ./spef/gpio_defaults_block.spef;
	read_spef -path gpio_defaults_block_37 ./spef/gpio_defaults_block.spef;
	read_spef ./spef/caravel.spef;
	read_sdc -echo ./sdc/caravel.sdc;
	report_checks -path_delay min -fields {slew cap input nets fanout} -format full_clock_expanded -group_count 50;
	report_checks -path_delay max -fields {slew cap input nets fanout} -format full_clock_expanded -group_count 50;
	report_worst_slack -max ;
	report_worst_slack -min ;
	echo " Management Area Interface ";
	report_checks -to soc/core_clk -unconstrained -group_count 1;
	echo " User project Interface ";
	report_checks -to mprj/wb_clk_i -unconstrained -group_count 1;
	report_checks -to mprj/wb_rst_i -unconstrained -group_count 1;
	report_checks -to mprj/wbs_cyc_i -unconstrained -group_count 1;
	report_checks -to mprj/wbs_stb_i -unconstrained -group_count 1;
	report_checks -to mprj/wbs_we_i -unconstrained -group_count 1;
	report_checks -to mprj/wbs_sel_i[*] -unconstrained -group_count 4;
	report_checks -to mprj/wbs_adr_i[*] -unconstrained -group_count 32;
	report_checks -to mprj/io_in[*] -unconstrained -group_count 32;
	report_checks -to mprj/user_clock2 -unconstrained -group_count 32;
	report_checks -to mprj/user_irq[*] -unconstrained -group_count 32;
	report_checks -to mprj/la_data_in[*] -unconstrained -group_count 128;
	report_checks -to mprj/la_oenb[*] -unconstrained -group_count 128;
	echo " Flash output Interface ";
	report_checks -to flash_clk -group_count 1;
	report_checks -to flash_csb -group_count 1;
	report_checks -to flash_io0 -group_count 1;
	


# report_checks -path_delay min  -format full_clock_expanded -fields {slew cap input nets fanout}
# report_checks -path_delay min  -format full_clock_expanded -fields {slew cap input nets fanout} -slack_max 0 -group_count 01
# report_checks -path_delay min  -format summary -slack_max 0 -group_count 1000
# report_checks -path_delay max  -format summary -slack_max 0 -group_count 1000

#  report_checks -path_delay min -through mprj/hack_soc/\soc.spi_video_ram_1.write_fifo.dffrf

# foreach pin [get_fanout -through mprj/hack_soc/clknet_leaf_11_wb_clk_i] {
# 	puts [get_full_name [$pin instance]]
# }


