# Run-time measurements

This directory contains the code corresponding to the experimental evaluation of the cost analysis.
It is organized as follows.

 - Directory `jlib/` contains the compiled Jasmin library. Go there first and run: `./generate.sh` and then `make`. This will create a static library `libjlib.a`
 - Directory `jlib-sys/` contains a Rust library exposing the functions from `libjlib`.
 - Directory `src/` contains safe wrappers around the `jlib-sys` library.
 - Directory `benches` contains the code to run the measurements.
 
The experiment can be run by calling the command: `nix-shell --run 'cargo bench'`
