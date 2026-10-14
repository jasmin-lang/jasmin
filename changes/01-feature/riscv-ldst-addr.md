- risc-v: the addresses of the loads and stores are checked in assembly
  generation against the encodable form: a base register and a signed
  12-bit offset (a load may also read a global). An address outside this
  form is now a compilation error instead of an assembler error.
