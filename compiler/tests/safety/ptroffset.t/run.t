The memory accesses through an input pointer must lie in a bounded range.

  $ ../../../jasmin-checksafety const_left.jazz 2>&1 | grep -e Violation -e line -e return -e safe -e "mem_pkp:"
  *** Possible Safety Violation(s):
    g return: bounded memory range of pkp
    mem_pkp: [-1/0; inf]
  Program is not safe!

  $ ../../../jasmin-checksafety counter_left.jazz 2>&1 | grep -e Violation -e line -e return -e safe -e "mem_pkp:"
  *** Possible Safety Violation(s):
    "counter_left.jazz", line 6 (41-53): is_valid p +64u (64u) 8 u64
    mem_pkp: [0; 0]
  Program is not safe!

  $ ../../../jasmin-checksafety counter_sub.jazz 2>&1 | grep -e Violation -e line -e return -e safe -e "mem_pkp:"
  *** Possible Safety Violation(s):
    "counter_sub.jazz", line 6 (41-53): is_valid p +64u (64u) 0 u64
    mem_pkp: [0; 0]
  Program is not safe!

Without widening thresholds, the range of the accesses in this loop is
unbounded, although each access is bounded.

  $ ../../../jasmin-checksafety --config nothreshold.json mask.jazz 2>&1 | grep -e Violation -e line -e return -e safe -e "mem_p:"
  *** Possible Safety Violation(s):
    g return: bounded memory range of p
    mem_p: [0; inf]
  Program is not safe!
