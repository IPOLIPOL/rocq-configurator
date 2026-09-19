Inductive Stage : Type :=
  | Stage3
  | Stage5
  | Tier4.

Inductive Power : Type :=
  | KVA250
  | KVA400
  | KVA560.

Inductive Frequency : Type :=
  | Hz50
  | Hz60.

Inductive DEFTank : Type :=
  | Tank7d
  | Tank10d
  | Tank14d.

Record Configuration : Type := {
  stage : Stage;
  power : Power;
  frequency : Frequency;
  def_tank : option DEFTank
}.

Definition requires_def (s : Stage) : bool :=
  match s with
  | Stage3 => false
  | Stage5 => true
  | Tier4 => true
  end.

Definition requires_dnv (s : Stage) : bool :=
  match s with
  | Stage3 => true
  | Stage5 => true
  | Tier4 => false
  end.

Definition requires_boem (s : Stage) : bool :=
  match s with
  | Stage3 => false
  | Stage5 => false
  | Tier4 => true
  end.

Definition valid_def_tank (c : Configuration) : bool :=
  match requires_def c.(stage), c.(def_tank) with
  | false, None => true
  | true, Some _ => true
  | _, _ => false
  end.

Definition validate (c : Configuration) : bool :=
  valid_def_tank c.

