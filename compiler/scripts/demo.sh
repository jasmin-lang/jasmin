#!/bin/bash

#./dmasm.native -p -t "typecheck" examples/25519-4limb/ladderstep.mil
./dmasm.native -t \
  "interp[n=4,rem_p=38][][test][]" \
  examples/25519-4limb/ladderstep.mil
