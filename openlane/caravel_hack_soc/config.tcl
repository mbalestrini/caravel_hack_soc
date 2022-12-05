#CONFIG ADAPTED FROM MPW3 - sky130



set ::env(PDK) "gf180mcuC"
set ::env(STD_CELL_LIBRARY) "gf180mcu_fd_sc_mcu7t5v0"

# User config
set script_dir [file dirname [file normalize [info script]]]

# name of your project, should also match the name of the top module
set ::env(DESIGN_NAME) caravel_hack_soc

# add your source files here
set ::env(VERILOG_FILES) "$::env(DESIGN_DIR)/../../verilog/rtl/caravel_hack_soc.v \
    $::env(DESIGN_DIR)/../../verilog/rtl/hack_soc/src/*.v"


# set ::env(VERILOG_INCLUDE_DIRS) "$::env(DESIGN_DIR)/../../verilog/rtl/hack_soc"

# target density, change this if you can't get your design to fit
# set ::env(PL_TARGET_DENSITY) 0.75

# Cell padding; increases the width of cells. 
# (Default: 4 microns -- 4 sites)
# set ::env(CELL_PAD) "0"

# Diode cell padding; increases the width of diode cells during placement checks.
# (Default: 2 microns -- 2 sites)
#set ::env(DIODE_PADDING) "2"


# set absolute size of the die to 300 x 300 um
set ::env(DIE_AREA) "0 0 600 600"
set ::env(FP_SIZING) absolute

# define number of IO pads
set ::env(SYNTH_DEFINES) "MPRJ_IO_PADS=38"

# clock period is ns
# 40ns would give us the 25MHz needed for the VGA video generator
set ::env(CLOCK_PERIOD) "40"  
set ::env(CLOCK_PORT) "wb_clk_i"

# macro needs to work inside Caravel, so can't be core and can't use metal 5
set ::env(DESIGN_IS_CORE) 0
set ::env(RT_MAXLAYER) {Metal4}

# You can draw more power domains if you need to 
set ::env(VDD_NETS) [list {vdd}]
set ::env(GND_NETS) [list {vss}]


# regular pin order seems to help with aggregating all the macros for the group project
#set ::env(FP_PIN_ORDER_CFG) $script_dir/pin_order.cfg

# turn off CVC as we have multiple power domains
set ::env(RUN_CVC) 0


# set ::env(PL_RESIZER_BUFFER_OUTPUT_PORTS) 0


# save some time
# set ::env(RUN_KLAYOUT_XOR) 0
# set ::env(RUN_KLAYOUT_DRC) 0


# set ::env(SYNTH_STRATEGY) "AREA 2"

# A flag that disables flattening the hierarchy during synthesis, only flattening it after synthesis, mapping and optimizations.
# Enabled = 1, Disabled = 0
# set ::env(SYNTH_NO_FLAT) 1

# set ::env(PL_RESIZER_HOLD_SLACK_MARGIN) 0.2
# set ::env(GLB_RESIZER_HOLD_SLACK_MARGIN) 0.2

set ::env(ROUTING_CORES) 16
#set ::env(ROUTING_OPT_ITERS) 80

#set ::env(BASE_SDC_FILE) "$::env(DESIGN_DIR)/caravel_hack_soc.sdc"
# set ::env(SYNTH_DRIVING_CELL) "sky130_fd_sc_hd__inv_8"
# set ::env(SYNTH_DRIVING_CELL_PIN) "Y"


set ::env(DIODE_INSERTION_STRATEGY) 3