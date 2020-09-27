


(* -------------------------Description--------------------------------------

   In this file we capture the notion of ordType. This type has
   elements with decidable equality. This is almost same and inspired by
   ssreflect library.  
   We also connect natural numbers and booleans to this type by creating
   canonical instances nat_eqType and bool_eqType. 
 

   Structure type: Type:=  Pack {
                             E: Type;
                             eqb: E-> E -> bool;
                             eqP: forall x y, reflect (eq x y)(eqb x y) }.

 
  Notation "x == y":= (@Decidable.eqb _ x y)(at level 70, no associativity).

 

  Some important results are:
  
  Lemma eqP  (T:ordType)(x y:T): reflect (x=y)(eqb  x y). 
  Lemma nat_eqP (x y:nat): reflect (x=y)(Nat.eqb x y).

  Canonical nat_eqType: eqType:=
                              {| Decidable.E:= nat; Decidable.eqb:= Nat.eqb;
                                  Decidable.eqP:= nat_eqP |}.

  Lemma bool_eqP (x y:bool): reflect (x=y)(Bool.eqb x y). 
  
  Canonical bool_eqType: eqType:= 
                             {| Decidable.E:= bool; Decidable.eqb:= Bool.eqb;
                                  Decidable.eqP:= bool_eqP |}.

  
   ------------------------------------------------------------------------- *)

From Coq Require Export ssreflect  ssrbool. 
Require Export  GenReflect Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Decidable.
  Structure type: Type:= Pack {
                             E: Type;
                             eqb: E-> E -> bool;
                             eqP: forall x y, reflect (eq x y)(eqb x y) }.
  Module Exports.
    Coercion E : type >-> Sortclass.
    Notation eqType:= type.
    End Exports.
End Decidable.
Export Decidable.Exports.

Notation "x == y":= (@Decidable.eqb _ x y)(at level 70, no associativity): bool_scope.



Lemma eqP  (T:eqType)(x y:T): reflect (x=y)(x == y). 
Proof. apply Decidable.eqP. Qed.


Hint Resolve eqP: core.

Lemma eq_to_eqb (T:eqType)(x y:T): (x=y)-> (x == y).
Proof.  intro; apply /eqP; auto. Qed.
Lemma eqb_to_eq (T:eqType) (x y:T): (x == y)-> (x=y).
Proof. intro;apply /eqP; auto. Qed.

Hint Immediate eq_to_eqb eqb_to_eq: core.

Lemma eq_refl (T: eqType)(x:T): x == x.
Proof. apply /eqP; auto. Qed.
Lemma eq_symm (T: eqType)(x y:T): (x == y)=(y == x).
Proof. { case (x== y) eqn:H1; case ( y== x) eqn:H2;  try(auto).
       { assert (H3: x=y). apply /eqP;auto.
         rewrite H3 in H2; rewrite eq_refl in H2; inversion H2. }
       { assert (H3: y= x). apply /eqP; auto.
         rewrite H3 in H1; rewrite eq_refl in H1; inversion H1.  } } Qed.

Hint Resolve eq_refl eq_symm: core.

(*--------- Natural numbers as an instance of eqType---------------------*)

Lemma nat_eqb_ref (x:nat): Nat.eqb x x = true.
Proof. induction x;simpl;auto. Qed.
Hint Resolve nat_eqb_ref:core.

Lemma nat_eqb_elim (x y:nat):  Nat.eqb x y -> x = y.
Proof. { revert y. induction x.
       { intro y. case y. tauto. simpl; intros n H; inversion H. }
       intro y. case y. simpl; intro H; inversion H. simpl. eauto. } Qed.
Hint Resolve nat_eqb_elim: core.

Lemma nat_eqb_intro (x y:nat): x=y -> Nat.eqb x y.
Proof. intro H. subst x. eauto. Qed.
Hint Resolve nat_eqb_intro: core.

Lemma nat_eqP (x y:nat): reflect (x=y)(Nat.eqb x y).
Proof. apply reflect_intro.  split; eauto. Qed. 
Hint Resolve nat_eqP: core.


Canonical nat_eqType: eqType:= {| Decidable.E:= nat; Decidable.eqb:= Nat.eqb;
                                  Decidable.eqP:= nat_eqP |}.

(*--------- Bool as an instance of eqType --------------------------------*)
Lemma bool_eqb_ref (x:bool): Bool.eqb x x = true.
Proof. destruct x; simpl; auto. Qed.
Hint Resolve bool_eqb_ref: core.

Lemma bool_eqb_elim (x y:bool): (Bool.eqb x y) -> x = y.
Proof. destruct x; destruct y; simpl; try (auto || tauto). Qed.

Lemma bool_eqb_intro (x y:bool): x = y -> (Bool.eqb x y).
Proof. intros; subst y; destruct x; simpl; auto. Qed.

Hint Immediate bool_eqb_elim bool_eqb_intro: core.

Lemma bool_eqP (x y:bool): reflect (x=y)(Bool.eqb x y).
Proof. apply reflect_intro.
       split. apply bool_eqb_intro. apply bool_eqb_elim. Qed.
Hint Resolve bool_eqP: core.

Canonical bool_eqType: eqType:= {| Decidable.E:= bool; Decidable.eqb:= Bool.eqb;
                                  Decidable.eqP:= bool_eqP |}.

Ltac conflict_eq :=
    match goal with
    | H:  (?x == ?x)= false  |- _
      => switch_in H; cut(False);[tauto |auto]
    | H: ~(is_true (?x == ?x)) |- _
      => cut(False);[tauto |auto]             
    | H: ~ (?x = ?x) |- _
      => cut(False);tauto
    | H: (?x == ?y) = true, H1: ?x <> ?y |- _
      => absurd (x = y);auto
    | H:  is_true (?x == ?y), H1: ?x <> ?y |- _
      => absurd (x = y);auto                     
    | H: (?x == ?y) = true, H1: ?y <> ?x |- _
      => absurd (y = x);[auto | (symmetry;auto)]
    | H: is_true (?x == ?y), H1: ?y <> ?x |- _
      => absurd (y = x);[auto | (symmetry;auto)]                     
    | H: (?x == ?y) = false, H1: ?x = ?y |- _
      => switch_in H; absurd (x=y); auto
    | H: (?x == ?y) = false, H1: ?y = ?x |- _
      => switch_in H; symmetry in H1; absurd (x=y); auto
    end.


