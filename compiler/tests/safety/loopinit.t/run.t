A loop is analysed until the initialization of the variables is stable too.

  $ ../../../jasmin-checksafety uninit.jazz 2>&1 | grep -e Violation -e line -e safe
  *** Possible Safety Violation(s):
    "uninit.jazz", line 15 (4-13): is_init d[0]
  Program is not safe!

  $ ../../../jasmin-checksafety init.jazz 2>&1 | grep -e Violation -e line -e safe
  *** No Safety Violation
