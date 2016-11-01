#! /usr/bin/python

from os import system
import os.path

verbose = True
debug = False
dmasm="./dmasm.native"
all_failed = []

class bcolors:
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'

def extract_enclosed(fname,marker):
    with open(fname) as f:
        lines = f.read().splitlines()
        inside = False
        start = "START:%s"%marker
        end = "END:%s"%marker
        enclosed=[]
        for l in lines:
            if not inside:
                if l == start:
                    inside = True
            else:
                if l == end:
                    return enclosed
                enclosed.append(l)
        raise "no terminator found"

def print_err(s):
    print bcolors.FAIL + s + bcolors.ENDC

def test(fname,get_error):

    if verbose:
        print "\n%s:"%(fname),

    fn_run_err = fname + ".run.err"
    fn_exp_err = fname + ".exp.err"
    fn_run_out = fname + ".run.out"
    fn_exp_out = fname + ".exp.out"

    # compose shell command
    arg = extract_enclosed(fname,"CMD")
    arg_set = ";\n".join(arg)
    cmd = 'sh -c \'%s;\n%s -t "$ARG" %s 2>%s.run.err >%s.run.out\''%(
             arg_set,dmasm,fname,fname,fname)

    # run and check error code
    if debug:
        print "%s"%cmd
    err = system(cmd)
    if (err != 0) != get_error:
        print_err("error, expected %s"%("error" if get_error else "success"))
        system("cat %s; cat %s"%(fn_run_out,fn_run_err))
        return

    # compare with expected output
    if not os.path.isfile(fn_exp_err) or not os.path.isfile(fn_exp_out):
        print "\n  create initial version by running"
        print "    cp %s %s"%(fn_run_err,fn_exp_err)
        print "    cp %s %s"%(fn_run_out,fn_exp_out)
    exp_err = open(fn_exp_err).read()
    run_err = open(fn_run_err).read()
    if exp_err!=run_err:
        print_err("error, wrong output on stderr")
        system("diff -u %s %s"%(fn_exp_err, fn_run_err))
        print "  run\n      cp %s %s\n  to use new definition"%(fn_run_err,fn_exp_err)
        return
    exp_out = open(fn_exp_out).read()
    run_out = open(fn_run_out).read()
    if exp_out!=run_out:
        print_err("error, wrong output on stdout")
        system("diff -u %s %s"%(fn_exp_out, fn_run_out))
        print "  run\n      cp %s %s\n  to use new definition"%(fn_run_out,fn_exp_out)
        return
    print bcolors.OKGREEN + "ok" + bcolors.ENDC,

def test_fail(fname):
    return test(fname,True)

def test_ok(fname):
    return test(fname,False)

def run(fname):
    arg = extract_enclosed(fname,"CMD")
    arg_set = ";\n".join(arg)
    cmd = 'time sh -c \'%s;\n%s -t "$ARG" %s\''%(arg_set,dmasm,fname)
    system(cmd)

def print_sep():
    print "\n\n%s"%("#"*70)

######################################################################

print_sep()

for fn in ["01","02","03","04","05","06","07","08","09","10","11","12","13","14"]:
    test_fail("tests/compiler/must_fail/t_%s.mil"%fn)


print_sep()

for fn in ["01"]:
    test_ok("tests/compiler/ok/t_%s.mil"%fn)

print_sep()
