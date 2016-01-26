#!/bin/bash

#./dmasm.native -p -t "typecheck,inline[bar]" tests/compiler/ok/t_01.mil 
#./dmasm.native -t \
#  "inline[ladderstep],print[test]" \
#  examples/25519-4limb/ladderstep.mil

###########################################################################

#ARG="inline[scalarmult],expand[scalarmult][rem_p=38]"
#ARG="$ARG,save[/tmp/unfold.mil][scalarmult]"
#ARG="$ARG,interp[rem_p=38][][test][]"
#
#./dmasm.native -t \
#  "$ARG"
#  examples/25519-4limb/ladderstep.mil

###########################################################################

ARG="inline[bar]"
ARG="$ARG,expand[bar][n=2]"
ARG="$ARG,array_assign_expand[bar]"
ARG="$ARG,array_expand[bar]"
ARG="$ARG,save[/tmp/a.mil][bar]"
ARG="$ARG,interp[n=2][][test][]"

./dmasm.native -t \
  "$ARG" \
  tests/compiler/ok/t_02.mil

#./dmasm.native -t \
#  "inline[scalarmult],expand[scalarmult][rem_p=38],save[test_unfold]" \
#  examples/25519-4limb/ladderstep.mil
