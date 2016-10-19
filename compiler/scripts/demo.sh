#!/bin/bash

set -x

#./dmasm.native -p -t "typecheck,inline[bar]" tests/compiler/ok/t_01.mil 
#./dmasm.native -t \
#  "inline[ladderstep],print[test]" \
#  examples/25519-4limb/ladderstep.mil

###########################################################################

#FUN="scalarmult"

ARG=""
ARG="inline[$FUN],expand[$FUN][rem_p=38]"
ARG="$ARG,array_assign_expand[$FUN]"
ARG="$ARG,save[/tmp/unfold.mil][$FUN]"
ARG="$ARG,array_expand[$FUN]"
ARG="$ARG,save[/tmp/unfold2.mil][$FUN]"
ARG="$ARG,interp[rem_p=38][][test][]"

#./dmasm.native -t \
#  "$ARG" \
#  examples/25519-4limb/ladderstep.mil

###########################################################################

#FUN="test"

#ARG="inline[$FUN],expand[$FUN][rem_p=38]"
#ARG="$ARG,array_expand[$FUN]"
#ARG="$ARG,save[/tmp/unfold.mil][$FUN]"

#./dmasm.native -t \
#  "$ARG" \
#  tests/compiler/must_fail/t_01.mil # also t_02.mil

###########################################################################

FUN="test"

ARG="register_liveness[$FUN]"
ARG="$ARG,save[/tmp/unfold.mil][$FUN]"

#./dmasm.byte -t \
#  "$ARG" \
#  tests/compiler/ok/t_06.mil

###########################################################################

FUN="test"

ARG="local_ssa[$FUN]"
ARG="register_allocate[$FUN][15]"
ARG="$ARG,save[/tmp/unfold.mil][$FUN]"

./dmasm.byte -t \
  "$ARG" \
  tests/compiler/ok/t_07.mil

###########################################################################

# ARG="inline[bar]"
# ARG="$ARG,expand[bar][n=2]"
# #ARG="$ARG,ssa[bar]"
# #ARG="$ARG,array_assign_expand[bar]"
# #ARG="$ARG,array_expand[bar]"
# ARG="$ARG,save[/tmp/a.mil][bar]"
# #ARG="$ARG,interp[n=2][][test][]"

# ./dmasm.native -t \
#   "$ARG" \
#   tests/compiler/ok/t_03.mil
# cat /tmp/a.mil

# #./dmasm.native -t \
# #  "inline[scalarmult],expand[scalarmult][rem_p=38],save[test_unfold]" \
# #  examples/25519-4limb/ladderstep.mil

