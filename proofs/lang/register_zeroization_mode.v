Record rzmode :=
  {
    rzm_flags : bool;
    rzm_registers : bool;
    rzm_xregisters : bool;
  }.

Definition rzm_none : rzmode :=
  {|
    rzm_flags := false;
    rzm_registers := false;
    rzm_xregisters := false;
  |}.

Definition rzm_regs : rzmode :=
  {|
    rzm_flags := false;
    rzm_registers := true;
    rzm_xregisters := false;
  |}.

Definition rzm_regs_flags : rzmode :=
  {|
    rzm_flags := true;
    rzm_registers := true;
    rzm_xregisters := false;
  |}.
