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
regs["R8"]  = {8: "%r8b", 16: "%r8w", 32 : "%r8d", 64 : "%r8"}
regs["R9"]  = {8: "%r9b", 16: "%r9w", 32 : "%r9d", 64 : "%r9"}
regs["R10"] = {8: "%r10b", 16: "%r10w", 32 : "%r10d", 64 : "%r10"}
regs["R11"] = {8: "%r11b", 16: "%r11w", 32 : "%r11d", 64 : "%r11"}
regs["R12"] = {8: "%r12b", 16: "%r12w", 32 : "%r12d", 64 : "%r12"}
regs["R13"] = {8: "%r13b", 16: "%r13w", 32 : "%r13d", 64 : "%r13"}
regs["R14"] = {8: "%r14b", 16: "%r14w", 32 : "%r14d", 64 : "%r14"}
regs["R15"] = {8: "%r15b", 16: "%r15w", 32 : "%r15d", 64 : "%r15"}

x86_conds           = {}
x86_conds["O_ct"]   = "o"
x86_conds["NO_ct"]  = "no"
x86_conds["B_ct"]   = "b"
x86_conds["NB_ct"]  = "nb"
x86_conds["E_ct"]   = "e"
x86_conds["NE_ct"]  = "ne"
x86_conds["BE_ct"]  = "be"
x86_conds["NBE_ct"] = "nbe"
x86_conds["S_ct"]   = "s"
x86_conds["NS_ct"]  = "ns"
x86_conds["P_ct"]   = "p"
x86_conds["NP_ct"]  = "np"
x86_conds["L_ct"]   = "l"
x86_conds["NL_ct"]  = "nl"
x86_conds["LE_ct"]  = "le"
x86_conds["NLE_ct"] = "nle"

ops_zero_arg            = {}
ops_zero_arg["CQO"]     = "cqo"
ops_zero_arg["LFENCE"]  = "lfence"
ops_zero_arg["MFENCE"]  = "mfence"
ops_zero_arg["SFENCE"]  = "sfence"

ops_one_arg             = {}
ops_one_arg["NEG"]      = "neg"
ops_one_arg["INC"]      = "inc"
ops_one_arg["DEC"]      = "dec"
ops_one_arg["MUL"]      = "mul"
ops_one_arg["DIV"]      = "div"
ops_one_arg["IMUL"]     = "imul"
ops_one_arg["IDIV"]     = "idiv"
ops_one_arg["NOT"]      = "not"
ops_one_arg["BSWAP"]    = "bswap"

ops_two_args            = {}
ops_two_args["ADD"]     = "add"
ops_two_args["ADC"]     = "adc"
ops_two_args["ADCX"]    = "adcx"
ops_two_args["ADOX"]    = "adox"
ops_two_args["SUB"]     = "sub"
ops_two_args["SBB"]     = "sbb"
ops_two_args["IMULr"]   = "imul"
ops_two_args["LZCNT"]   = "lzcnt"
ops_two_args["AND"]     = "and"
ops_two_args["OR"]      = "or"
ops_two_args["XOR"]     = "xor"
ops_two_args["POPCNT"]  = "popcnt"
ops_two_args["CMP"]     = "cmp"
ops_two_args["TEST"]    = "test"
ops_two_args["MOV"]     = "mov"
# ops_two_args["MOVSX"]   = "movsx"
# ops_two_args["MOVZX"]   = "movzx"
# ops_two_args["CMOVcc"]  = "cmov"

ops_three_args                  = {}
ops_three_args["ANDN"]          = "andn"
ops_three_args["PEXT"]          = "pext"
ops_three_args["PDEP"]          = "pdep"
ops_three_args["MULX_lo_hi"]    = "mulx"

size_variations     = {}
size_variations[8]  = ["_8", "b"]
size_variations[16] = ["_16", "w"]
size_variations[32] = ["_32", "l"]
size_variations[64] = ["_64", "q"]


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

regs_list = list(regs.keys())

def gen_zero_arg_instrs():
    for op in ops_zero_arg:
        folder_name = op
        mv_to_folder = move_build_to_out_dir + "/" + folder_name
        if mv_to_folder in test_folders:
            continue
        test_folders.add(mv_to_folder)
        jazz_instr = op
        asm_instr = ops_zero_arg[op]
        print(jazz_instr)
        print(asm_instr)

        # TODO: improve this later
        with open(my_asm_orig, "r") as reader:
            with open(my_asm_final, "w") as writer:
                line = reader.read()
                final_line = line.replace("replace_me", asm_instr)
                writer.write(final_line)
        with open(op_args_file, "w") as writer:
            j_op = op
            writer.write(j_op)
        os.system(make_clean_cmd)
        os.system(make_build_cmd)
        os.system(mv_to_folder)

def gen_one_arg_instrs():
    for op in ops_one_arg:
        for size in size_variations:
            # these are currently not supported in Jasmin
            if size == 8 and ( op == "MUL" or op == "IMUL" or op == "DIV" or op == "IDIV"):
                continue

            if op == "BSWAP" and (size == 8 or size == 16):
                continue

            for _ in range(1):
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

def gen_two_arg_instrs():
    for op in ops_two_args:
        for size in size_variations:

            if size == 8 and (op == "IMULr" or op == "LZCNT" or op == "POPCNT"):
                continue

            if (op == "ADCX" or op == "ADOX") and (size == 8 or size == 16):
                continue

            for num in range(2):
                reg1 = get_usable_reg(regs_list)
                reg2 = get_usable_reg(regs_list)
                if num == 1:
                    reg2 = reg1             # uses the same register as both operands
                folder_name = op + size_variations[size][0] + "_" + reg1 + "_" + reg2
                mv_to_folder = move_build_to_out_dir + "/" + folder_name
                if mv_to_folder in test_folders:
                    continue
                test_folders.add(mv_to_folder)
                jazz_instr = "{}{}\t{} {}".format(op, size_variations[size][0], reg1, reg2)
                print(jazz_instr)
                asm_instr = "{}{}\t{}, {}".format(ops_two_args[op], size_variations[size][1], regs[reg2][size], regs[reg1][size])
                print(asm_instr)

                # TODO: improve this later
                with open(my_asm_orig, "r") as reader:
                    with open(my_asm_final, "w") as writer:
                        line = reader.read()
                        final_line = line.replace("replace_me", asm_instr)
                        writer.write(final_line)
                with open(op_args_file, "w") as writer:
                    j_op = "{}{}".format(op, size_variations[size][0])
                    j_args = reg1 + " " + reg2
                    writer.write(j_op + "\n" + j_args)
                os.system(make_clean_cmd)
                os.system(make_build_cmd)
                os.system(mv_to_folder)

def gen_three_arg_instrs():
    for op in ops_three_args:
        for size in size_variations:

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
                folder_name = op + size_variations[size][0] + "_" + reg1 + "_" + reg2 + "_" + reg3
                mv_to_folder = move_build_to_out_dir + "/" + folder_name
                if mv_to_folder in test_folders:
                    continue
                test_folders.add(mv_to_folder)
                jazz_instr = "{}{}\t{} {} {}".format(op, size_variations[size][0], reg1, reg2, reg3)
                print(jazz_instr)
                asm_instr = "{}{}\t{}, {}, {}".format(ops_three_args[op], size_variations[size][1], regs[reg3][size], regs[reg2][size], regs[reg1][size])
                print(asm_instr)

                # TODO: improve this later
                with open(my_asm_orig, "r") as reader:
                    with open(my_asm_final, "w") as writer:
                        line = reader.read()
                        final_line = line.replace("replace_me", asm_instr)
                        writer.write(final_line)
                with open(op_args_file, "w") as writer:
                    j_op = "{}{}".format(op, size_variations[size][0])
                    j_args = reg1 + " " + reg2 + " " + reg3
                    writer.write(j_op + "\n" + j_args)
                os.system(make_clean_cmd)
                os.system(make_build_cmd)
                os.system(mv_to_folder)

def gen_cmovcc_instrs():
    cmov_map = {"CMOVcc" : "cmov"}
    op = "CMOVcc"
    for size in size_variations:
        if size == 8:
            continue

        for cond in x86_conds:
            for num in range(2):
                reg1 = get_usable_reg(regs_list)
                reg2 = get_usable_reg(regs_list)
                if num == 1:
                    reg2 = reg1             # uses the same register as both operands
                folder_name = op + size_variations[size][0] + "_" + cond + "_" + reg1 + "_" + reg2
                mv_to_folder = move_build_to_out_dir + "/" + folder_name
                if mv_to_folder in test_folders:
                    continue
                test_folders.add(mv_to_folder)
                jazz_instr = "{}{}\t{} {} {}".format(op, size_variations[size][0], cond, reg1, reg2)
                print(jazz_instr)
                asm_instr = "{}{}\t{}, {}".format(cmov_map[op], x86_conds[cond], regs[reg2][size], regs[reg1][size])
                print(asm_instr)

                # TODO: improve this later
                with open(my_asm_orig, "r") as reader:
                    with open(my_asm_final, "w") as writer:
                        line = reader.read()
                        final_line = line.replace("replace_me", asm_instr)
                        writer.write(final_line)
                with open(op_args_file, "w") as writer:
                    j_op = "{}{}".format(op, size_variations[size][0])
                    j_args = cond + " " + reg1 + " " + reg2
                    writer.write(j_op + "\n" + j_args)
                os.system(make_clean_cmd)
                os.system(make_build_cmd)
                os.system(mv_to_folder)


if __name__ == "__main__":
    # gen_zero_arg_instrs()
    # gen_one_arg_instrs()
    # gen_two_arg_instrs()
    # gen_three_arg_instrs()
    gen_cmovcc_instrs()
