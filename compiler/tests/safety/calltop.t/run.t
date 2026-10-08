With the CallTopHeuristic call policy, a callee without memory access is
analyzed once per call site, from top.

  $ ../../../jasmin-checksafety --config calltop.json first_call.jazz 2>&1 | grep -e Violation -e line -e safe
  *** No Safety Violation

The abstraction of a callee is reused at the next evaluations of its call site.

  $ ../../../jasmin-checksafety --config calltop.json reuse.jazz 2>&1 | grep -e Violation -e line -e safe
  *** No Safety Violation

A callee may branch, in an if or in a conditional move.

  $ ../../../jasmin-checksafety --config calltop.json if.jazz 2>&1 | grep -e Violation -e line -e safe
  *** No Safety Violation

  $ ../../../jasmin-checksafety --config calltop.json cmov.jazz 2>&1 | grep -e Violation -e line -e safe
  *** No Safety Violation

The safety conditions of the callee and of the caller are still checked.

  $ ../../../jasmin-checksafety --config calltop.json div.jazz 2>&1 | grep -e Violation -e line -e safe
  *** Possible Safety Violation(s):
    "div.jazz", line 5 (2-12): x <>64 (64u) 0
  Program is not safe!

  $ ../../../jasmin-checksafety --config calltop.json index.jazz 2>&1 | grep -e Violation -e line -e safe
  *** Possible Safety Violation(s):
    "index.jazz", line 15 (2-11): in_bound: t[a] (length 32 U8)
  Program is not safe!
