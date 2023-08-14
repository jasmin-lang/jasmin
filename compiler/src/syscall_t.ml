type 'a syscall_t =
  | RandomBytes of 'a
  | Open of 'a