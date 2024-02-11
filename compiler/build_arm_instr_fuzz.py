#! /usr/bin/python3

import os
import argparse
import random
import arm_isa

test_folders = set()
# TODO: Need to make it general later
op_args_file = "entry/op_args_arm.txt"
asm_instr_file = "entry/asm_instr_arm.txt"

make_clean_cmd          = "make clean;"
make_build_cmd          = "make -j;"
make_out_dir_cmd        = "mkdir -p "
move_build_to_out_dir   = "mv -f _build/default/entry/ "


parser = argparse.ArgumentParser()
parser.add_argument('out_dir', type=str, help='A required out directory argument')

args = parser.parse_args()
make_out_dir_cmd += args.out_dir
move_build_to_out_dir += args.out_dir

# create that dir which will contain all the builds
os.system(make_out_dir_cmd)

regs_list = list(arm_isa.regs.keys())

def get_usable_reg (rlist):
    choice = random.choice(rlist)
    while (choice == "lr" or choice == "sp"):
        choice = random.choice(rlist)
    return choice

# currently only going to support with emulator
def gen_build_dir(mv_to_folder, j_instr, asm_instr):
    print("Building Instruction: ", asm_instr)
    with open(op_args_file, "w") as writer:
        writer.write(j_instr)
    with open(asm_instr_file, "w") as writer:
        writer.write(asm_instr)
    os.system(make_clean_cmd)
    os.system(make_build_cmd)
    os.system(mv_to_folder)

def gen_two_arg_instrs():
    for op in arm_isa.ops_two_args:
        for num in range(2):
            reg1 = get_usable_reg(regs_list)
            reg2 = get_usable_reg(regs_list)

            # create some variations
            if num == 1:
                reg2 = reg1

            folder_name = op + "_" + reg1 + "_" + reg2
            mv_to_folder = move_build_to_out_dir + "/" + folder_name
            if mv_to_folder in test_folders:
                continue
            test_folders.add(mv_to_folder)
            asm_instr = "{}\t{}, {}".format(arm_isa.ops_two_args[op], arm_isa.regs[reg1], arm_isa.regs[reg2])
            j_op = op
            j_args = reg1 + " " + reg2
            j_instr = j_op + "\n" + j_args
            gen_build_dir(mv_to_folder, j_instr, asm_instr)    

def gen_three_arg_instrs():
    for op in arm_isa.ops_three_args:
        for num in range(5):
            reg1 = get_usable_reg(regs_list)
            reg2 = get_usable_reg(regs_list)
            reg3 = get_usable_reg(regs_list)

            # create some variations
            if num == 1:
                reg2 = reg1
            if num == 2:
                reg3 = reg1
            if num == 3:
                reg3 = reg2
            if num == 4:
                reg2 = reg1
                reg3 = reg1

            folder_name = op + "_" + reg1 + "_" + reg2 + "_" + reg3 
            mv_to_folder = move_build_to_out_dir + "/" + folder_name
            if mv_to_folder in test_folders:
                continue
            test_folders.add(mv_to_folder)
            asm_instr = "{}\t{}, {}, {}".format(arm_isa.ops_three_args[op], arm_isa.regs[reg1], arm_isa.regs[reg2], arm_isa.regs[reg3])
            j_op = op
            j_args = reg1 + " " + reg2 + " " + reg3
            j_instr = j_op + "\n" + j_args
            gen_build_dir(mv_to_folder, j_instr, asm_instr)

def gen_four_arg_instrs():
    for op in arm_isa.ops_four_args:
        for num in range(7):
            reg1 = get_usable_reg(regs_list)
            reg2 = get_usable_reg(regs_list)
            reg3 = get_usable_reg(regs_list)
            reg4 = get_usable_reg(regs_list)

            # create some variations
            if num == 1:
                reg2 = reg1
            if num == 2:
                reg3 = reg1
            if num == 3:
                reg3 = reg2
            if num == 4:
                reg2 = reg1
                reg3 = reg1
            if num == 5:
                reg3 = reg1
                reg4 = reg1
            if num == 6:
                reg2 = reg1
                reg3 = reg1
                reg4 = reg1

            folder_name = op + "_" + reg1 + "_" + reg2 + "_" + reg3 + "_" + reg4
            mv_to_folder = move_build_to_out_dir + "/" + folder_name
            if mv_to_folder in test_folders:
                continue
            test_folders.add(mv_to_folder)
            asm_instr = "{}\t{}, {}, {}, {}".format(arm_isa.ops_four_args[op], arm_isa.regs[reg1], arm_isa.regs[reg2], arm_isa.regs[reg3], arm_isa.regs[reg4])
            j_op = op
            j_args = reg1 + " " + reg2 + " " + reg3 + " " + reg4
            j_instr = j_op + "\n" + j_args
            gen_build_dir(mv_to_folder, j_instr, asm_instr)


if __name__ == "__main__":
    gen_four_arg_instrs()
	
