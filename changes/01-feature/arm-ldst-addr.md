- arm-m4: the addresses of the loads and stores (LDR, STR and the narrow
  and signed forms) are checked in assembly generation against the Thumb-2
  encodings: an immediate offset in [-255, 4095], or a register offset
  shifted by 0 to 3. An address outside these forms is now a compilation
  error instead of an assembler error.
