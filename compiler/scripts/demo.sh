#!/bin/bash

#./dmasm.native -p -t "typecheck,inline[bar]" tests/compiler/ok/t_01.mil 
#./dmasm.native -t \
#  "inline[ladderstep],print[test]" \
#  examples/25519-4limb/ladderstep.mil

./dmasm.native -t \
  "inline[scalarmult],expand[scalarmult][rem_p=38],save[/tmp/unfold.mil][scalarmult],interp[rem_p=38][][test][]" \
  examples/25519-4limb/ladderstep.mil

# ,expand[scalarmult][rem_p=38]

#./dmasm.native -t \
#  "inline[scalarmult],expand[scalarmult][rem_p=38],save[test_unfold]" \
#  examples/25519-4limb/ladderstep.mil
