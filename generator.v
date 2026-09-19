Record Configuration : Type := {
  stage3 : Prop;
  stage5 : Prop;
  tier4  : Prop;

  kva250 : Prop;
  kva400 : Prop;
  kva560 : Prop;

  hz50 : Prop;
  hz60 : Prop;

  def : Prop;
  tank7d : Prop;
  tank10d : Prop;
  tank14d : Prop;

  dnv : Prop;
  boem : Prop
}.

(* Helper function *)
Definition exactlyOne (a b c : Prop) : Prop :=
  (a \/ b \/ c) /\
  ~ (a /\ b) /\
  ~ (a /\ c) /\
  ~ (b /\ c).

Definition Valid (c : Configuration) : Prop :=
  exactlyOne c.(stage3) c.(stage5) c.(tier4) /\
  exactlyOne c.(kva250) c.(kva400) c.(kva560) /\
  (c.(hz50) \/ c.(hz60)) /\
  ~ (c.(hz50) /\ c.(hz60)) /\
  ((c.(stage5) \/ c.(tier4)) -> c.(def)) /\
  ((c.(def)) -> exactlyOne c.(tank7d) c.(tank10d) c.(tank14d)) /\
  ((c.(stage3) \/ c.(stage5)) -> c.(dnv)) /\
  (c.(tier4) -> c.(boem)).

(* valid configuration *)
Definition config1 : Configuration := {|
  stage3 := False;
  stage5 := True;
  tier4 := False;

  kva250 := False;
  kva400 := True;
  kva560 := False;

  hz50 := True;
  hz60 := False;

  def := True;
  tank7d := False;
  tank10d := True;
  tank14d := False;

  dnv := True;
  boem := False
|}.

(* invalid configuration *)
Definition config2 : Configuration := {|
  stage3 := False;
  stage5 := True;
  tier4 := False;

  kva250 := False;
  kva400 := True;
  kva560 := False;

  hz50 := True;
  hz60 := False;

  def := False;
  tank7d := False;
  tank10d := False;
  tank14d := False;

  dnv := True;
  boem := False
|}.