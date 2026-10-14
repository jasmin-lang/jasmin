- armv8a: the addresses of the loads and stores (LDR, STR and the narrow
  forms) are checked in assembly generation against the encodable forms:
  an unsigned offset that is a multiple of the access size up to 4095 times
  it, an unscaled offset in [-256, 255] (the LDUR/STUR encodings), or a
  register offset shifted by the access size or not shifted. An address
  outside these forms is now a compilation error instead of an assembler
  error.
