PWDD := $(shell pwd)
BLOCKS := $(shell basename $(PWDD))


# ---- Include Partitioned Makefiles ----

CONFIG = caravel_user_project

export COCOTB_REDUCED_LOG_FMT=1
export LIBPYTHON_LOC=$(shell cocotb-config --libpython)


include $(MCW_ROOT)/verilog/dv/make/env.makefile
include $(MCW_ROOT)/verilog/dv/make/var.makefile
include $(MCW_ROOT)/verilog/dv/make/cpu.makefile
include $(MCW_ROOT)/verilog/dv/make/sim.makefile


# Changed this values from the ones from the .makefiles because the name of the root caravel_user_project folder was different (caravel_hack_soc)
VERILOG_PATH = $(MCW_ROOT)/verilog
USER_PROJECT_VERILOG = $(MCW_ROOT)/../verilog

coco_test: wrapped_hack_soc_test.hex
	rm -rf sim_build/
	mkdir sim_build/

	iverilog -Ttyp -DFUNCTIONAL -DSIM -DUSE_POWER_PINS -DUNIT_DELAY=#1 \
	-f$(VERILOG_PATH)/includes/includes.rtl.caravel \
	-f$(USER_PROJECT_VERILOG)/includes/includes.rtl.$(CONFIG) -o sim_build/sim.vvp wrapped_hack_soc_test_tb.v

	TESTCASE=test_all MODULE=wrapped_hack_soc_test vvp -M $$(cocotb-config --prefix)/cocotb/libs -m libcocotbvpi_icarus sim_build/sim.vvp
	! grep failure results.xml

coco_test_gl: wrapped_hack_soc_test.hex
	rm -rf sim_build/
	mkdir sim_build/

	iverilog -Ttyp -DFUNCTIONAL -DSIM -DUSE_POWER_PINS -DUNIT_DELAY=#1 \
	-f$(VERILOG_PATH)/includes/includes.rtl.caravel \
	-f$(USER_PROJECT_VERILOG)/includes/includes.gl.$(CONFIG) -o sim_build/sim.vvp wrapped_hack_soc_test_tb.v

	TESTCASE=test_all_gl MODULE=wrapped_hack_soc_test vvp -M $$(cocotb-config --prefix)/cocotb/libs -m libcocotbvpi_icarus sim_build/sim.vvp
	! grep failure results.xml



##############################################################################
# Comiple firmeware
##############################################################################
%.elf: %.c $(LINKER_SCRIPT) $(SOURCE_FILES)
	${GCC_PATH}/${GCC_PREFIX}-gcc -O3 -g \
	-I$(FIRMWARE_PATH) \
	-I$(VERILOG_PATH)/dv/generated \
	-I$(VERILOG_PATH)/dv/ \
	-I$(VERILOG_PATH)/common \
	  $(CPUFLAGS) \
	-Wl,-Bstatic,-T,$(LINKER_SCRIPT),--strip-debug \
	-ffreestanding -nostdlib -o $@ $(SOURCE_FILES) $<

%.lst: %.elf
	${GCC_PATH}/${GCC_PREFIX}-objdump -d -S $< > $@

%.hex: %.elf
	${GCC_PATH}/${GCC_PREFIX}-objcopy -O verilog $< $@ 
	# to fix flash base address
	sed -ie 's/@10/@00/g' $@

%.bin: %.elf
	${GCC_PATH}/${GCC_PREFIX}-objcopy -O binary $< /dev/stdout | tail -c +1048577 > $@




# PATTERN = wrapped_hack_soc_test


# all: coco_test # ${PATTERN:=.vcd}

# hex:  ${PATTERN:=.hex}

# coco_test: ${PATTERN}.hex
# 	rm -rf sim_build/
# 	mkdir sim_build/

# 	iverilog -Ttyp -DFUNCTIONAL -DSIM -DUSE_POWER_PINS -DUNIT_DELAY=#1 \
# 	-f$(VERILOG_PATH)/includes/includes.rtl.caravel \
# 	-f$(USER_PROJECT_VERILOG)/includes/includes.rtl.$(CONFIG) -o sim_build/sim.vvp $(PATTERN)_tb.v

# 	TESTCASE=test_start,test_all MODULE=$(PATTERN) vvp -M $$(cocotb-config --prefix)/cocotb/libs -m libcocotbvpi_icarus sim_build/sim.vvp
# 	! grep failure results.xml



# coco_test: ${PATTERN}.hex
# 	rm -rf sim_build/
# 	mkdir sim_build/
# 	iverilog -o sim_build/sim.vvp -s $(PATTERN)_tb $(PATTERN)_tb.v -DSIM -DFUNCTIONAL $(DUMP_TRACE) \
# 	-I $(PDK_PATH) \
# 	-I $(CARAVEL_BEHAVIOURAL_MODELS) -I $(CARAVEL_RTL_PATH) \
# 	-I $(UPRJ_BEHAVIOURAL_MODELS)    -I $(UPRJ_RTL_PATH) \
# 	-I $(HACK_SOC_PATH)/src  \
	
# 	MODULE=$(PATTERN) vvp -M $$(cocotb-config --prefix)/cocotb/libs -m libcocotbvpi_icarus sim_build/sim.vvp
# 	! grep failure results.xml


# %.vvp: %_tb.v %.hex
# ifeq ($(SIM),RTL)
# 	iverilog -DFUNCTIONAL -DSIM -I $(PDK_PATH) \
# 	-I $(CARAVEL_BEHAVIOURAL_MODELS) -I $(CARAVEL_RTL_PATH) \
# 	-I $(UPRJ_BEHAVIOURAL_MODELS)    -I $(UPRJ_RTL_PATH) \
# 	-I $(HACK_SOC_PATH)/src  $(HACK_SOC_SOURCES) \
# 	$< -o $@ 
# 	! grep failure results.xml
# else  
# 	iverilog -DFUNCTIONAL -DSIM -DGL -I $(PDK_PATH) \
# 	-I $(CARAVEL_BEHAVIOURAL_MODELS) -I $(CARAVEL_RTL_PATH) -I $(CARAVEL_VERILOG_PATH) \
# 	-I $(UPRJ_BEHAVIOURAL_MODELS) -I$(UPRJ_RTL_PATH)   -I $(UPRJ_VERILOG_PATH) \
# 	-I $(HACK_SOC_PATH)/src $(HACK_SOC_SOURCES) \
# 	$< -o $@ 
# 	! grep failure results.xml
# endif


# %.vcd: %.vvp
# 	vvp $<

# %.elf: %.c caravel_test_hack_program.c $(CARAVEL_FIRMWARE_PATH)/sections.lds $(CARAVEL_FIRMWARE_PATH)/start.s
# 	${GCC_PATH}/${GCC_PREFIX}-gcc -O3 -I $(CARAVEL_PATH) -march=rv32imc -mabi=ilp32 -Wl,-Bstatic,-T,$(CARAVEL_FIRMWARE_PATH)/sections.lds,--strip-debug -ffreestanding -nostdlib -o $@ $(CARAVEL_FIRMWARE_PATH)/start.s $<

# %.hex: %.elf
# 	${GCC_PATH}/${GCC_PREFIX}-objcopy -O verilog $< $@ 
# 	# to fix flash base address
# 	sed -i 's/@10000000/@00000000/g' $@

# %.bin: %.elf
# 	${GCC_PATH}/${GCC_PREFIX}-objcopy -O binary $< /dev/stdout | tail -c +1048577 > $@

# ---- Clean ----

# clean:
# 	rm -f *.elf *.hex *.bin *.vvp *.vcd *.log results.xml

# .PHONY: clean hex all





# ## Caravel Pointers
# CARAVEL_ROOT ?= ../../../caravel
# CARAVEL_PATH ?= $(CARAVEL_ROOT)
# CARAVEL_FIRMWARE_PATH = $(CARAVEL_PATH)/verilog/dv/caravel
# CARAVEL_VERILOG_PATH  = $(CARAVEL_PATH)/verilog
# CARAVEL_RTL_PATH = $(CARAVEL_VERILOG_PATH)/rtl
# CARAVEL_BEHAVIOURAL_MODELS = $(CARAVEL_VERILOG_PATH)/dv/caravel

# ## User Project Pointers
# UPRJ_VERILOG_PATH ?= ../../../verilog
# UPRJ_RTL_PATH = $(UPRJ_VERILOG_PATH)/rtl
# UPRJ_BEHAVIOURAL_MODELS = ../

# WRAPPED_HACK_SOC_PATH = ../../rtl/wrapped_hack_soc
# HACK_SOC_PATH = $(WRAPPED_HACK_SOC_PATH)/hack_soc


# DUMP_TRACE = 

# ## RISCV GCC 
# GCC_PATH?=/ef/apps/bin
# GCC_PREFIX?=riscv32-unknown-elf
# PDK_PATH?=/ef/tech/SW/sky130A

# ## Simulation mode: RTL/GL
# SIM?=RTL

# # include the modules that cocotb needs for test
# export PYTHONPATH := $(UPRJ_RTL_PATH)/wrapped_frequency_counter/frequency_counter/test
# export COCOTB_REDUCED_LOG_FMT=1
# export LIBPYTHON_LOC=$(shell cocotb-config --libpython)


# .SUFFIXES:

# PATTERN = wrapped_hack_soc_test

# all: coco_test # ${PATTERN:=.vcd}

# hex:  ${PATTERN:=.hex}

# coco_test_with_trace:
# 	make coco_test DUMP_TRACE=-DDUMP_TRACE
	


# coco_test: ${PATTERN}.hex
# 	rm -rf sim_build/
# 	mkdir sim_build/
# 	iverilog -o sim_build/sim.vvp -s $(PATTERN)_tb $(PATTERN)_tb.v -DSIM -DFUNCTIONAL $(DUMP_TRACE) \
# 	-I $(PDK_PATH) \
# 	-I $(CARAVEL_BEHAVIOURAL_MODELS) -I $(CARAVEL_RTL_PATH) \
# 	-I $(UPRJ_BEHAVIOURAL_MODELS)    -I $(UPRJ_RTL_PATH) \
# 	-I $(HACK_SOC_PATH)/src  \
	
# 	MODULE=$(PATTERN) vvp -M $$(cocotb-config --prefix)/cocotb/libs -m libcocotbvpi_icarus sim_build/sim.vvp
# 	! grep failure results.xml


# %.vvp: %_tb.v %.hex
# ifeq ($(SIM),RTL)
# 	iverilog -DFUNCTIONAL -DSIM -I $(PDK_PATH) \
# 	-I $(CARAVEL_BEHAVIOURAL_MODELS) -I $(CARAVEL_RTL_PATH) \
# 	-I $(UPRJ_BEHAVIOURAL_MODELS)    -I $(UPRJ_RTL_PATH) \
# 	-I $(HACK_SOC_PATH)/src  $(HACK_SOC_SOURCES) \
# 	$< -o $@ 
# 	! grep failure results.xml
# else  
# 	iverilog -DFUNCTIONAL -DSIM -DGL -I $(PDK_PATH) \
# 	-I $(CARAVEL_BEHAVIOURAL_MODELS) -I $(CARAVEL_RTL_PATH) -I $(CARAVEL_VERILOG_PATH) \
# 	-I $(UPRJ_BEHAVIOURAL_MODELS) -I$(UPRJ_RTL_PATH)   -I $(UPRJ_VERILOG_PATH) \
# 	-I $(HACK_SOC_PATH)/src $(HACK_SOC_SOURCES) \
# 	$< -o $@ 
# 	! grep failure results.xml
# endif

# %.vcd: %.vvp
# 	vvp $<

# %.elf: %.c caravel_test_hack_program.c $(CARAVEL_FIRMWARE_PATH)/sections.lds $(CARAVEL_FIRMWARE_PATH)/start.s
# 	${GCC_PATH}/${GCC_PREFIX}-gcc -O3 -I $(CARAVEL_PATH) -march=rv32imc -mabi=ilp32 -Wl,-Bstatic,-T,$(CARAVEL_FIRMWARE_PATH)/sections.lds,--strip-debug -ffreestanding -nostdlib -o $@ $(CARAVEL_FIRMWARE_PATH)/start.s $<

# %.hex: %.elf
# 	${GCC_PATH}/${GCC_PREFIX}-objcopy -O verilog $< $@ 
# 	# to fix flash base address
# 	sed -i 's/@10000000/@00000000/g' $@

# %.bin: %.elf
# 	${GCC_PATH}/${GCC_PREFIX}-objcopy -O binary $< /dev/stdout | tail -c +1048577 > $@

# # ---- Clean ----

# clean:
# 	rm -f *.elf *.hex *.bin *.vvp *.vcd *.log results.xml

# .PHONY: clean hex all
