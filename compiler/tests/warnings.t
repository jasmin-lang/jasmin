  $ ../jasminc -wea -arch riscv warning/risc-v/load_constant_warning.jazz
  warning: support of the RISC-V architecture is experimental
  "warning/risc-v/load_constant_warning.jazz", line 3 (9-15)
  warning: extra assignment introduced:
             ra = #LI(((32u) 10)); /* :r */

  $ ../jasminc -wea warning/x86-64/extra_assignment.jazz
  "warning/x86-64/extra_assignment.jazz", line 9 (2-12)
  from line 15 (2-12)
  warning: extra assignment introduced:
             RAX = #MOV_64(((64u) 0)); /* :r */

  $ ../jasminc -wlea warning/x86-64/lea.jazz
  "warning/x86-64/lea.jazz", line 6 (2-18)
  warning: LEA instruction is used

  $ ../jasminc warning/x86-64/reg_const_ptr.jazz
  "warning/x86-64/reg_const_ptr.jazz", line 2 (9-10)
  warning: no need to return a [reg const ptr] r

  $ ../jasminc -wall -until_cstexp fail/linter/dead_variables.jazz
  "fail/linter/dead_variables.jazz", line 6 (8-18)
  warning: Instruction only assigns dead variables
  "fail/linter/dead_variables.jazz", line 11 (2-8)
  warning: Instruction only assigns dead variables
  "fail/linter/dead_variables.jazz", line 23 (4-28)
  warning: Variable “y” is affected but never used
  "fail/linter/dead_variables.jazz", line 32 (4-10)
  warning: Instruction only assigns dead variables
  "fail/linter/dead_variables.jazz", line 37 (8-12)
  warning: Instruction only assigns dead variables
  "fail/linter/dead_variables.jazz", line 65 (4-10)
  warning: Instruction only assigns dead variables
  "fail/linter/dead_variables.jazz", line 76 (12-22)
  warning: Instruction only assigns dead variables
  "fail/linter/dead_variables.jazz", line 87 (2-11)
  warning: Instruction only assigns dead variables
  "fail/linter/dead_variables.jazz", line 106 (2-18)
  warning: Instruction only assigns dead variables
  "fail/linter/dead_variables.jazz", line 111 (2-14)
  warning: Instruction only assigns dead variables

  $ ../jasminc -wall fail/linter/variables_initialisation.jazz
  "fail/linter/variables_initialisation.jazz", line 3 (5-6)
  warning: Variable p (declared at : "fail/linter/variables_initialisation.jazz", line 2 (12-13)) not initialized
  "fail/linter/variables_initialisation.jazz", line 8 (4-9)
  warning: Variable state (declared at : "fail/linter/variables_initialisation.jazz", line 7 (20-25)) not initialized
  "fail/linter/variables_initialisation.jazz", line 13 (11-12)
  warning: Variable r (declared at : "fail/linter/variables_initialisation.jazz", line 12 (12-13)) not initialized
  "fail/linter/variables_initialisation.jazz", line 18 (14-15)
  warning: Variable x (declared at : "fail/linter/variables_initialisation.jazz", line 17 (12-13)) not initialized
  "fail/linter/variables_initialisation.jazz", line 18 (16-17)
  warning: Variable x (declared at : "fail/linter/variables_initialisation.jazz", line 17 (12-13)) not initialized
  "fail/linter/variables_initialisation.jazz", line 25 (11-12)
  warning: Variable x (declared at : "fail/linter/variables_initialisation.jazz", line 22 (12-13)) not initialized
  "fail/linter/variables_initialisation.jazz", line 8 (4-17)
  warning: Instruction only assigns dead variables
  "fail/linter/variables_initialisation.jazz", line 18 (4-18)
  warning: Instruction only assigns dead variables

  $ ../jasminc -wall fail/linter/bug_1223.jazz
  "fail/linter/bug_1223.jazz", line 3 (2-21)
  warning: Variable “z” is affected but never used
  "fail/linter/bug_1223.jazz", line 23 (2-22)
  warning: Variable “c” is affected but never used
