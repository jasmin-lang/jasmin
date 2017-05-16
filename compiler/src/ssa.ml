open Prog

let split_live_ranges (f: 'info func) : 'info func =
  let lf = Liveness.live_fd f in
  f

let remove_phi_nodes (f: 'info func) : 'info func =
  f
