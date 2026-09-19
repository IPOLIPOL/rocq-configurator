Definition holds (b : bool) : Prop := b = true.
Coercion holds : bool >-> Sortclass.

Record Configuration : Type := {
  stage3 : bool;
  stage5 : bool;
  tier4  : bool;

  kva250 : bool;
  kva400 : bool;
  kva560 : bool;

  hz50 : bool;
  hz60 : bool;

  def : bool;
  tank7d : bool;
  tank10d : bool;
  tank14d : bool;

  dnv : bool;
  boem : bool
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
  stage3 := false;
  stage5 := true;
  tier4 := false;

  kva250 := false;
  kva400 := true;
  kva560 := false;

  hz50 := true;
  hz60 := false;

  def := true;
  tank7d := false;
  tank10d := true;
  tank14d := false;

  dnv := true;
  boem := false
|}.

(* invalid configuration *)
Definition config2 : Configuration := {|
  stage3 := false;
  stage5 := true;
  tier4 := false;

  kva250 := false;
  kva400 := true;
  kva560 := false;

  hz50 := true;
  hz60 := false;

  def := false;
  tank7d := false;
  tank10d := false;
  tank14d := false;

  dnv := true;
  boem := false
|}.

(* ---- Decision machinery: written once, never touched again ---- *)
Definition dec (P : Prop) := {P} + {~ P}.

Definition dec_atom (b : bool) : dec (holds b).
Proof. destruct b; unfold holds; [ left; reflexivity | right; discriminate ]. Defined.

Definition dec_not {P} (p : dec P) : dec (~ P) :=
  match p with
  | left a  => right (fun n => n a)
  | right n => left n
  end.

Definition dec_and {P Q} (p : dec P) (q : dec Q) : dec (P /\ Q) :=
  match p, q with
  | left a,  left b  => left (conj a b)
  | right n, _       => right (fun h => n (proj1 h))
  | _,       right n => right (fun h => n (proj2 h))
  end.

Definition dec_or {P Q} (p : dec P) (q : dec Q) : dec (P \/ Q) :=
  match p, q with
  | left a,  _       => left (or_introl a)
  | _,       left b  => left (or_intror b)
  | right n, right m => right (fun h => match h with or_introl a => n a | or_intror b => m b end)
  end.

Definition dec_imp {P Q} (p : dec P) (q : dec Q) : dec (P -> Q) :=
  match p, q with
  | _,       left b  => left (fun _ => b)
  | left a,  right n => right (fun h => n (h a))
  | right n, right _ => left (fun a => match n a with end)
  end.

Definition Valid_dec (c : Configuration) : dec (Valid c).
Proof.
  unfold Valid, exactlyOne, dec.
  repeat first [ apply dec_and | apply dec_or | apply dec_not | apply dec_imp | apply dec_atom ].
Defined.

Definition valid (c : Configuration) : bool :=
  if Valid_dec c then true else false.