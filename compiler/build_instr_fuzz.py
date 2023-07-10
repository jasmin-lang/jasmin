#! /usr/bin/python3

import os
import argparse
import random

test_folders = set()
# TODO: Need to make it general later
op_args_file = "entry/op_args.txt"
my_asm_orig = "entry/libfoo/myasm_orig.s"
my_asm_final = "entry/libfoo/myasm.s"

regs = {}
regs["RAX"] = {8: "%al", 16: "%ax", 32 : "%eax", 64 : "%rax"}
regs["RCX"] = {8: "%cl", 16: "%cx", 32 : "%ecx", 64 : "%rcx"}
regs["RDX"] = {8: "%dl", 16: "%dx", 32 : "%edx", 64 : "%rdx"}
regs["RBX"] = {8: "%bl", 16: "%bx", 32 : "%ebx", 64 : "%rbx"}
regs["RSP"] = {8: "%spl", 16: "%sp", 32 : "%esp", 64 : "%rsp"}
regs["RBP"] = {8: "%bpl", 16: "%bp", 32 : "%ebp", 64 : "%rbp"}
regs["RSI"] = {8: "%sil", 16: "%si", 32 : "%esi", 64 : "%rsi"}
regs["RDI"] = {8: "%dil", 16: "%di", 32 : "%edi", 64 : "%rdi"}
regs["R8"] = {8: "%r8b", 16: "%r8w", 32 : "%r8d", 64 : "%r8"}
regs["R9"] = {8: "%r9b", 16: "%r9w", 32 : "%r9d", 64 : "%r9"}
regs["R10"] = {8: "%r10b", 16: "%r10w", 32 : "%r10d", 64 : "%r10"}
regs["R11"] = {8: "%r11b", 16: "%r11w", 32 : "%r11d", 64 : "%r11"}
regs["R12"] = {8: "%r12b", 16: "%r12w", 32 : "%r12d", 64 : "%r12"}
regs["R13"] = {8: "%r13b", 16: "%r13w", 32 : "%r13d", 64 : "%r13"}
regs["R14"] = {8: "%r14b", 16: "%r14w", 32 : "%r14d", 64 : "%r14"}
regs["R15"] = {8: "%r15b", 16: "%r15w", 32 : "%r15d", 64 : "%r15"}

ops_one_arg = {}
# ops_one_arg["NEG"] = "neg"
# ops_one_arg["INC"] = "inc"
# ops_one_arg["DEC"] = "dec"
ops_one_arg["MUL"] = "mul"
ops_one_arg["DIV"] = "div"

ops_two_args = {}
# ops_two_args["ADD"] = "add"
# ops_two_args["SUB"] = "sub"
ops_two_args["DIV"] = "div"

size_variations = {}
size_variations[8] = ["_8", "b"]
size_variations[16] = ["_16", "w"]
size_variations[32] = ["_32", "l"]
size_variations[64] = ["_64", "q"]


make_clean_cmd = "make clean;"
make_build_cmd = "make -j;"
make_out_dir_cmd = "mkdir -p "
move_build_to_out_dir = "mv -f _build/default/entry/ "


parser = argparse.ArgumentParser()
parser.add_argument('out_dir', type=str, help='A required out directory argument')

args = parser.parse_args()
make_out_dir_cmd += args.out_dir
move_build_to_out_dir += args.out_dir

# create that dir which will contain all the builds
os.system(make_out_dir_cmd)

def get_usable_reg (rlist):
    choice = random.choice(rlist)
    while (choice == "RSP" or choice == "RBP"):
        choice = random.choice(rlist)
    return choice

regs_list = list(regs.keys())


for op in ops_one_arg:
    for size in size_variations:
        for num in range(2):
            reg = get_usable_reg(regs_list)
            folder_name = op + size_variations[size][0] + "_" + reg
            mv_to_folder = move_build_to_out_dir + "/" + folder_name
            if mv_to_folder in test_folders:
                continue
            test_folders.add(mv_to_folder)
            jazz_instr = "{}{}\t{}".format(op, size_variations[size][0], reg)
            print(jazz_instr)
            asm_instr = "{}{}\t{}".format(ops_one_arg[op], size_variations[size][1], regs[reg][size])
            print(asm_instr)

            # TODO: improve this later
            with open(my_asm_orig, "r") as reader:
                with open(my_asm_final, "w") as writer:
                    line = reader.read()
                    final_line = line.replace("replace_me", asm_instr)
                    writer.write(final_line)
            with open(op_args_file, "w") as writer:
                j_op = "{}{}".format(op, size_variations[size][0])
                j_args = reg
                writer.write(j_op + "\n" + j_args)
            os.system(make_clean_cmd)
            os.system(make_build_cmd)
            os.system(mv_to_folder)


# for op in ops_two_args:
#     for size in size_variations:
#         for num in range(1):
#             reg1 = get_usable_reg(regs_list)
#             reg2 = get_usable_reg(regs_list)
#             folder_name = op + size_variations[size][0] + "_" + reg1 + "_" + reg2
#             mv_to_folder = move_build_to_out_dir + "/" + folder_name
#             if mv_to_folder in test_folders:
#                 continue
#             test_folders.add(mv_to_folder)
#             jazz_instr = "{}{}\t{} {}".format(op, size_variations[size][0], reg1, reg2)
#             print(jazz_instr)
#             asm_instr = "{}{}\t{}, {}".format(ops_two_args[op], size_variations[size][1], regs[reg2][size], regs[reg1][size])
#             print(asm_instr)

#             # TODO: improve this later
#             with open(my_asm_orig, "r") as reader:
#                 with open(my_asm_final, "w") as writer:
#                     line = reader.read()
#                     final_line = line.replace("replace_me", asm_instr)
#                     writer.write(final_line)
#             with open(op_args_file, "w") as writer:
#                 j_op = "{}{}".format(op, size_variations[size][0])
#                 j_args = reg1 + " " + reg2
#                 writer.write(j_op + "\n" + j_args)
#             os.system(make_clean_cmd)
#             os.system(make_build_cmd)
#             os.system(mv_to_folder)