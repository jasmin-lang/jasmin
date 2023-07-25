#! /usr/bin/python3

import os
import argparse
import random
import x86_isa

test_folders = set()
# TODO: Need to make it general later
op_args_file = "entry/op_args.txt"
my_asm_orig = "entry/libfoo/myasm_orig.s"
my_asm_final = "entry/libfoo/myasm.s"

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

def get_usable_reg (rlist):
    choice = random.choice(rlist)
    while (choice == "RSP" or choice == "RBP"):
        choice = random.choice(rlist)
    return choice

regs_list = list(x86_isa.regs.keys())

def gen_build_dir(mv_to_folder, j_instr, asm_instr):
    print("Building Instruction: ", asm_instr)
    with open(my_asm_orig, "r") as reader:
            with open(my_asm_final, "w") as writer:
                line = reader.read()
                final_line = line.replace("replace_me", asm_instr)
                writer.write(final_line)
    with open(op_args_file, "w") as writer:
        writer.write(j_instr)
    os.system(make_clean_cmd)
    os.system(make_build_cmd)
    os.system(mv_to_folder)

def gen_zero_arg_instrs():
    for op in x86_isa.ops_zero_arg:
        folder_name = op
        mv_to_folder = move_build_to_out_dir + "/" + folder_name
        if mv_to_folder in test_folders:
            continue
        test_folders.add(mv_to_folder)
        asm_instr = x86_isa.ops_zero_arg[op]
        j_instr = op
        gen_build_dir(mv_to_folder, j_instr, asm_instr)

def gen_one_arg_instrs():
    for op in x86_isa.ops_one_arg:
        for size in x86_isa.size_variations:
            # 8 bit MUL/MULX not supported in Jasmin
            if size == 8 and ( op == "MUL" or op == "IMUL" or op == "DIV" or op == "IDIV"):
                continue

            if op == "BSWAP" and (size == 8 or size == 16):
                continue

            for _ in range(1):
                reg = get_usable_reg(regs_list)
                folder_name = op + "_" + x86_isa.size_variations[size][0] + "_" + reg
                mv_to_folder = move_build_to_out_dir + "/" + folder_name
                if mv_to_folder in test_folders:
                    continue
                test_folders.add(mv_to_folder)
                asm_instr = "{}{}\t{}".format(x86_isa.ops_one_arg[op], x86_isa.size_variations[size][1], x86_isa.regs[reg][size])
                j_op = "{}_{}".format(op, x86_isa.size_variations[size][0])
                j_args = reg
                j_instr = j_op + "\n" + j_args
                gen_build_dir(mv_to_folder, j_instr, asm_instr)

def gen_two_arg_instrs():
    for op in x86_isa.ops_two_args:
        for size in x86_isa.size_variations:
            if size == 8 and (op == "IMULr" or op == "LZCNT" or op == "POPCNT" or op == "BT"):
                continue

            if (op == "ADCX" or op == "ADOX") and (size == 8 or size == 16):
                continue

            for num in range(2):
                reg1 = get_usable_reg(regs_list)
                reg2 = get_usable_reg(regs_list)
                if num == 1:
                    reg2 = reg1             # uses the same register as both operands
                folder_name = op + "_" + x86_isa.size_variations[size][0] + "_" + reg1 + "_" + reg2
                mv_to_folder = move_build_to_out_dir + "/" + folder_name
                if mv_to_folder in test_folders:
                    continue
                test_folders.add(mv_to_folder)
                asm_instr = "{}{}\t{}, {}".format(x86_isa.ops_two_args[op], x86_isa.size_variations[size][1], x86_isa.regs[reg2][size], x86_isa.regs[reg1][size])
                j_op = "{}_{}".format(op, x86_isa.size_variations[size][0])
                j_args = reg1 + " " + reg2
                j_instr = j_op + "\n" + j_args
                gen_build_dir(mv_to_folder, j_instr, asm_instr)

def gen_two_arg_two_size_instrs():
    sizes = [(16, 8), (32, 8), (64, 8), (32, 16), (64, 16)]
    for op in x86_isa.ops_two_args_two_sizes:
        for (size1, size2) in sizes:
            for num in range(2):
                reg1 = get_usable_reg(regs_list)
                reg2 = get_usable_reg(regs_list)
                if num == 1:
                    reg2 = reg1
                folder_name = op + "_u" + x86_isa.size_variations[size1][0] + "u" + x86_isa.size_variations[size2][0] + "_" + reg1 + "_" + reg2
                mv_to_folder = move_build_to_out_dir + "/" + folder_name
                if mv_to_folder in test_folders:
                    continue
                test_folders.add(mv_to_folder)
                asm_instr = "{}{}{}\t{}, {}".format(x86_isa.ops_two_args_two_sizes[op], x86_isa.size_variations[size2][1], x86_isa.size_variations[size1][1], x86_isa.regs[reg2][size2], x86_isa.regs[reg1][size1])
                j_op = "{}_u{}u{}".format(op, x86_isa.size_variations[size1][0], x86_isa.size_variations[size2][0])
                j_args = reg1 + " " + reg2
                j_instr = j_op + "\n" + j_args
                gen_build_dir(mv_to_folder, j_instr, asm_instr)

def gen_three_arg_instrs():
    for op in x86_isa.ops_three_args:
        for size in x86_isa.size_variations:

            # currently the existing ops don't support these sizes
            if size == 8 or size == 16:
                continue

            for num in range(5):
                reg1 = get_usable_reg(regs_list)
                reg2 = get_usable_reg(regs_list)
                reg3 = get_usable_reg(regs_list)
                #create some variations
                if num == 1:
                    reg2 = reg1
                if num == 2:
                    reg3 = reg1
                if num == 3:
                    reg3 = reg2
                if num == 4:
                    reg2 = reg1
                    reg3 = reg1
                folder_name = op + "_" + x86_isa.size_variations[size][0] + "_" + reg1 + "_" + reg2 + "_" + reg3
                mv_to_folder = move_build_to_out_dir + "/" + folder_name
                if mv_to_folder in test_folders:
                    continue
                test_folders.add(mv_to_folder)
                asm_instr = "{}{}\t{}, {}, {}".format(x86_isa.ops_three_args[op], x86_isa.size_variations[size][1], x86_isa.regs[reg3][size], x86_isa.regs[reg2][size], x86_isa.regs[reg1][size])
                j_op = "{}_{}".format(op, x86_isa.size_variations[size][0])
                j_args = reg1 + " " + reg2 + " " + reg3
                j_instr = j_op + "\n" + j_args
                gen_build_dir(mv_to_folder, j_instr, asm_instr)

def gen_setcc_instrs():
    set_map = {"SETcc" : "set"}
    op = "SETcc"
    size = 8
    for cond in x86_isa.x86_conds:
        for _ in range(2):
            reg1 = get_usable_reg(regs_list)
           # uses the same register as both operands
            folder_name = op + "_" + x86_isa.size_variations[size][0] + "_" + cond + "_" + reg1
            mv_to_folder = move_build_to_out_dir + "/" + folder_name
            if mv_to_folder in test_folders:
                continue
            test_folders.add(mv_to_folder)
            asm_instr = "{}{}\t{}".format(set_map[op], x86_isa.x86_conds[cond], x86_isa.regs[reg1][size])
            j_op = "{}".format(op)
            j_args = cond + " " + reg1
            j_instr = j_op + "\n" + j_args
            gen_build_dir(mv_to_folder, j_instr, asm_instr)

def gen_cmovcc_instrs():
    cmov_map = {"CMOVcc" : "cmov"}
    op = "CMOVcc"
    for size in x86_isa.size_variations:
        if size == 8:
            continue

        for cond in x86_isa.x86_conds:
            for num in range(2):
                reg1 = get_usable_reg(regs_list)
                reg2 = get_usable_reg(regs_list)
                if num == 1:
                    reg2 = reg1             # uses the same register as both operands
                folder_name = op + "_" + x86_isa.size_variations[size][0] + "_" + cond + "_" + reg1 + "_" + reg2
                mv_to_folder = move_build_to_out_dir + "/" + folder_name
                if mv_to_folder in test_folders:
                    continue
                test_folders.add(mv_to_folder)
                asm_instr = "{}{}\t{}, {}".format(cmov_map[op], x86_isa.x86_conds[cond], x86_isa.regs[reg2][size], x86_isa.regs[reg1][size])
                j_op = "{}_{}".format(op, x86_isa.size_variations[size][0])
                j_args = cond + " " + reg1 + " " + reg2
                j_instr = j_op + "\n" + j_args
                gen_build_dir(mv_to_folder, j_instr, asm_instr)


if __name__ == "__main__":
    gen_zero_arg_instrs()
    gen_one_arg_instrs()
    gen_two_arg_instrs()
    gen_three_arg_instrs()
    gen_cmovcc_instrs()
    gen_setcc_instrs()
    gen_two_arg_two_size_instrs()
