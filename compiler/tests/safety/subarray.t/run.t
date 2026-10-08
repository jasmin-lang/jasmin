A copy from a slice at an unknown offset, or into one, carries the
uninitialized cells of its source.

  $ ../../../jasmin-checksafety copy.jazz 2>&1 | grep -e Violation -e line -e safe
  *** Possible Safety Violation(s):
    "copy.jazz", line 17 (2-12): is_init e[3]
  Program is not safe!

  $ ../../../jasmin-checksafety write.jazz 2>&1 | grep -e Violation -e line -e safe
  *** Possible Safety Violation(s):
    "write.jazz", line 14 (2-11): is_init t[1]
  Program is not safe!

  $ ../../../jasmin-checksafety write_init.jazz 2>&1 | grep -e Violation -e line -e safe
  *** No Safety Violation

  $ ../../../jasmin-checksafety loop.jazz 2>&1 | grep -e Violation -e line -e safe
  *** Possible Safety Violation(s):
    "loop.jazz", line 21 (4-13): is_init b[0]
  Program is not safe!

A copy from a slice at an unknown offset of an initialized array is
initialized. Global arrays are initialized.

  $ ../../../jasmin-checksafety global.jazz 2>&1 | grep -e Violation -e line -e safe
  *** No Safety Violation

  $ ../../../jasmin-checksafety local.jazz 2>&1 | grep -e Violation -e line -e safe
  *** No Safety Violation

  $ ../../../jasmin-checksafety partial.jazz 2>&1 | grep -e Violation -e line -e safe
  *** Possible Safety Violation(s):
    "partial.jazz", line 12 (2-11): is_init e[3]
  Program is not safe!

  $ ../../../jasmin-checksafety loop_alias.jazz 2>&1 | grep -e Violation -e line -e safe
  *** Possible Safety Violation(s):
    "loop_alias.jazz", line 19 (4-13): is_init b[0]
  Program is not safe!

A string written into a slice initializes the cells of the slice.

  $ ../../../jasmin-checksafety string.jazz 2>&1 | grep -e Violation -e line -e safe
  *** Possible Safety Violation(s):
    "string.jazz", line 6 (2-17): is_init t[0]
  Program is not safe!

  $ ../../../jasmin-checksafety string_init.jazz 2>&1 | grep -e Violation -e line -e safe
  *** No Safety Violation

  $ ../../../jasmin-checksafety string_value.jazz 2>&1 | grep -e Violation -e line -e safe
  *** Possible Safety Violation(s):
    "string_value.jazz", line 11 (2-11): in_bound: a[x] (length 64 U8)
  Program is not safe!
