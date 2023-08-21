#! /usr/bin/python3

import os
import argparse
import random
import x86_isa

test_folders = set()
# TODO: Need to make it general later
op_args_file = "entry/op_args.txt"
asm_instr_file = "entry/asm_instr.txt"
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

def get_usable_xreg (xrlist):
    return random.choice(xrlist)

regs_list = list(x86_isa.regs.keys())
xregs_list = list(x86_isa.xregs.keys())

def gen_build_dir(mv_to_folder, j_instr, asm_instr):
    print("Building Instruction: ", asm_instr)
    with open(my_asm_orig, "r") as reader:
            with open(my_asm_final, "w") as writer:
                line = reader.read()
                final_line = line.replace("replace_me", asm_instr)
                writer.write(final_line)
    with open(op_args_file, "w") as writer:
        writer.write(j_instr)
    with open(asm_instr_file, "w") as writer:
        writer.write(asm_instr)
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

def gen_one_arg_imm8_instrs():
    # this is very boring and need to reduce it later to make the
    # immediate dynamic
    imm8_list = range(256)
    for op in x86_isa.ops_one_arg_imm8:
        for size in x86_isa.size_variations:
            for _ in range(1):
                for _ in range(5):
                    i = random.choice(imm8_list)
                    reg = get_usable_reg(regs_list)
                    folder_name = op + "_" + x86_isa.size_variations[size][0] + "_" + reg + "_" + str(i)
                    mv_to_folder = move_build_to_out_dir + "/" + folder_name
                    if mv_to_folder in test_folders:
                        continue
                    test_folders.add(mv_to_folder)
                    asm_instr = "{}{}\t${}, {}".format(x86_isa.ops_one_arg_imm8[op], x86_isa.size_variations[size][1], str(hex(i)), x86_isa.regs[reg][size])
                    j_op = "{}_{}".format(op, x86_isa.size_variations[size][0])
                    j_args = reg + " " + str(i)
                    j_instr = j_op + "\n" + j_args
                    gen_build_dir(mv_to_folder, j_instr, asm_instr)

def gen_two_arg_imm8_instrs():
    # this is very boring and need to reduce it later to make the
    # immediate dynamic
    imm8_list = range(256)
    for op in x86_isa.ops_two_arg_imm8:
        for size in x86_isa.size_variations:
            if size == 8:
                continue
            for num in range(2):
                for _ in range(5):
                    i = random.choice(imm8_list)
                    reg1 = get_usable_reg(regs_list)
                    reg2 = get_usable_reg(regs_list)
                    if num == 1:
                        reg2 = reg1
                    folder_name = op + "_" + x86_isa.size_variations[size][0] + "_" + reg1 + "_" + reg2 + "_" + str(i)
                    mv_to_folder = move_build_to_out_dir + "/" + folder_name
                    if mv_to_folder in test_folders:
                        continue
                    test_folders.add(mv_to_folder)
                    asm_instr = "{}{}\t${}, {}, {}".format(x86_isa.ops_two_arg_imm8[op], x86_isa.size_variations[size][1], str(hex(i)), x86_isa.regs[reg2][size], x86_isa.regs[reg1][size])
                    j_op = "{}_{}".format(op, x86_isa.size_variations[size][0])
                    j_args = reg1 + " " + reg2 + " " + str(i)
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

def gen_two_args_vec_instrs():
    for op in x86_isa.ops_two_args_vec:
        for size in [128, 256]:

            for num in range(2):
                xreg1 = get_usable_xreg(xregs_list)
                xreg2 = get_usable_xreg(xregs_list)
                if num == 1:
                    xreg2 = xreg1             # uses the same register as both operands
                folder_name = op + "_" + str(size) + "_" + xreg1 + "_" + xreg2
                mv_to_folder = move_build_to_out_dir + "/" + folder_name
                if mv_to_folder in test_folders:
                    continue
                test_folders.add(mv_to_folder)
                asm_instr = "{}\t{}, {}".format(x86_isa.ops_two_args_vec[op], x86_isa.xregs[xreg2][size], x86_isa.xregs[xreg1][size])
                j_op = "{}_{}".format(op, str(size))
                j_args = xreg1 + " " + xreg2
                j_instr = j_op + "\n" + j_args
                gen_build_dir(mv_to_folder, j_instr, asm_instr)

def gen_two_arg_imm8_vec_instrs():
    imm8_list = range(256)
    for op in x86_isa.ops_two_arg_imm8_vec:
        for size in [128, 256]:
            if size == 128 and op == "VPERMQ":
                continue
            for num in range(2):
                for _ in range(5):
                    i = random.choice(imm8_list)
                    xreg1 = get_usable_xreg(xregs_list)
                    xreg2 = get_usable_xreg(xregs_list)
                    if num == 1:
                        xreg2 = xreg1
                    folder_name = op + "_" + str(size) + "_" + xreg1 + "_" + xreg2 + "_" + str(i)
                    mv_to_folder = move_build_to_out_dir + "/" + folder_name
                    if mv_to_folder in test_folders:
                        continue
                    test_folders.add(mv_to_folder)
                    asm_instr = "{}\t${}, {}, {}".format(x86_isa.ops_two_arg_imm8_vec[op], str(hex(i)), x86_isa.xregs[xreg2][size], x86_isa.xregs[xreg1][size])
                    j_op = "{}_{}".format(op, str(size))
                    if op == "VPERMQ":
                        j_op = op
                    j_args = xreg1 + " " + xreg2 + " " + str(i)
                    j_instr = j_op + "\n" + j_args
                    gen_build_dir(mv_to_folder, j_instr, asm_instr)

def gen_three_arg_vec_instrs():
    for op in x86_isa.ops_three_args_vec:
        for size in [128, 256]:                  # TODO: handle 256 later
            for num in range(5):
                xreg1 = get_usable_xreg(xregs_list)
                xreg2 = get_usable_xreg(xregs_list)
                xreg3 = get_usable_xreg(xregs_list)
                #create some variations
                if num == 1:
                    xreg2 = xreg1
                if num == 2:
                    xreg3 = xreg1
                if num == 3:
                    xreg3 = xreg2
                if num == 4:
                    xreg2 = xreg1
                    xreg3 = xreg1
                folder_name = op + "_" + str(size) + "_" + xreg1 + "_" + xreg2 + "_" + xreg3
                mv_to_folder = move_build_to_out_dir + "/" + folder_name
                if mv_to_folder in test_folders:
                    continue
                test_folders.add(mv_to_folder)
                asm_instr = "{}\t{}, {}, {}".format(x86_isa.ops_three_args_vec[op], x86_isa.xregs[xreg3][size], x86_isa.xregs[xreg2][size], x86_isa.xregs[xreg1][size])
                j_op = "{}_{}".format(op, size)
                j_args = xreg1 + " " + xreg2 + " " + xreg3
                j_instr = j_op + "\n" + j_args
                gen_build_dir(mv_to_folder, j_instr, asm_instr)


def gen_three_arg128_vec_size_instrs():
    for op in x86_isa.ops_three_args_vec128_size:
        for size in [128]:
            for num in range(5):
                xreg1 = get_usable_xreg(xregs_list)
                xreg2 = get_usable_xreg(xregs_list)
                xreg3 = get_usable_xreg(xregs_list)
                #create some variations
                if num == 1:
                    xreg2 = xreg1
                if num == 2:
                    xreg3 = xreg1
                if num == 3:
                    xreg3 = xreg2
                if num == 4:
                    xreg2 = xreg1
                    xreg3 = xreg1
                folder_name = op + "_" + str(size) + "_" + xreg1 + "_" + xreg2 + "_" + xreg3
                mv_to_folder = move_build_to_out_dir + "/" + folder_name
                if mv_to_folder in test_folders:
                    continue
                test_folders.add(mv_to_folder)
                asm_instr = "{}\t{}, {}, {}".format(x86_isa.ops_three_args_vec128_size[op], x86_isa.xregs[xreg3][size], x86_isa.xregs[xreg2][size], x86_isa.xregs[xreg1][size])
                j_op = "{}".format(op)
                j_args = xreg1 + " " + xreg2 + " " + xreg3
                j_instr = j_op + "\n" + j_args
                gen_build_dir(mv_to_folder, j_instr, asm_instr)

def gen_four_arg_vec_instrs():
    for op in x86_isa.ops_four_args_vec:
        for size in [128, 256]:                  # TODO: handle 256 later
            for num in range(6):
                xreg1 = get_usable_xreg(xregs_list)
                xreg2 = get_usable_xreg(xregs_list)
                xreg3 = get_usable_xreg(xregs_list)
                xreg4 = get_usable_xreg(xregs_list)
                #create some variations
                if num == 1:
                    xreg2 = xreg1
                if num == 2:
                    xreg3 = xreg1
                if num == 3:
                    xreg3 = xreg2
                if num == 4:
                    xreg2 = xreg1
                    xreg3 = xreg1
                if num == 5:
                    xreg2 = xreg1
                    xreg3 = xreg1 
                    xreg4 = xreg1
                folder_name = op + "_" + str(size) + "_" + xreg1 + "_" + xreg2 + "_" + xreg3 + "_" + xreg4
                mv_to_folder = move_build_to_out_dir + "/" + folder_name
                if mv_to_folder in test_folders:
                    continue
                test_folders.add(mv_to_folder)
                asm_instr = "{}\t{}, {}, {}, {}".format(x86_isa.ops_four_args_vec[op], x86_isa.xregs[xreg4][size], x86_isa.xregs[xreg3][size], x86_isa.xregs[xreg2][size], x86_isa.xregs[xreg1][size])
                j_op = "{}_{}".format(op, size)
                j_args = xreg1 + " " + xreg2 + " " + xreg3 + " " + xreg4
                j_instr = j_op + "\n" + j_args
                gen_build_dir(mv_to_folder, j_instr, asm_instr)


if __name__ == "__main__":
    # gen_zero_arg_instrs()
    # gen_one_arg_instrs()
    # gen_two_arg_instrs()
    # gen_three_arg_instrs()
    # gen_cmovcc_instrs()
    # gen_setcc_instrs()
    # gen_two_arg_two_size_instrs()
    # gen_one_arg_imm8_instrs()
    # gen_two_arg_imm8_instrs()
    # gen_three_arg_vec_instrs()
    # gen_two_args_vec_instrs()
    # gen_two_arg_imm8_vec_instrs()
    # gen_three_arg128_vec_size_instrs()
    gen_four_arg_vec_instrs()