


(* -----------------Description------------------------------------------

This file contains useful results about reflection techniques in Coq. 
Some of the important concepts formalized are:

Definition Prop_bool_eq (P: Prop) (b: bool):= P <-> b=true.
Lemma reflect_intro (P:Prop)(b:bool): Prop_bool_eq P b -> reflect P b.

Lemma impP(p q:bool): reflect (p->q)((negb p) || q).
Lemma switch1(b:bool): b=false -> ~ b. 
Lemma switch2(b:bool): ~ b -> b=false.


Some useful Ltac defined terms:

 Ltac switch:=  (apply switch1||apply switch2).
 Ltac switch_in H:= (apply switch1 in H || apply switch2 in H).
 Ltac right_ := apply /orP; right.
 Ltac left_ := apply /orP; left.
 Ltac split_ := apply /andP; split.   

--------------------- ------------------- ------------------------------*)



From Coq Require Export ssreflect  ssrbool.

Require Export Lia.


Set Implicit Arguments.

Section GeneralReflections.
Definition Prop_bool_eq (P: Prop) (b: bool):= P <-> b=true.

(* Inductive reflect (P : Prop) : bool -> Set :=  
   ReflectT : P -> reflect P true | ReflectF : ~ P -> reflect P false *)
Lemma reflect_elim (P:Prop)(b: bool): reflect P b -> Prop_bool_eq P b.
Proof. { intro H.
       split. case H; [ auto | discriminate || contradiction ].
       case H; [ auto | discriminate || contradiction ]. } Qed. 
Lemma reflect_intro (P:Prop)(b:bool): Prop_bool_eq P b -> reflect P b.
Proof. { intros. destruct H as  [H1 H2].
         destruct b. constructor;auto.
         constructor.  intro H. apply H1 in H;inversion H. } Qed.

Lemma reflect_dec P: forall b:bool, reflect P b -> {P} + {~P}.
Proof. intros b H; destruct b; inversion H; auto.  Qed.
Lemma reflect_EM P: forall b:bool, reflect P b -> P \/ ~P.
Proof. intros b H. case H; tauto. Qed.
Lemma dec_EM P: {P}+{~P} -> P \/ ~P.
  Proof. intro H; destruct H as [Hl |Hr];tauto. Qed.
Lemma pbe_EM P: forall b:bool, Prop_bool_eq P b -> P \/ ~P.
Proof. { intros b H; cut( reflect P b).
         apply reflect_EM. apply reflect_intro;auto. } Qed.


(* iffP : forall (P Q : Prop) (b : bool), reflect P b -> (P -> Q) -> (Q -> P) -> reflect Q b *)

(* idP : forall b1 : bool, reflect b1 b1 *)

(* negP
     : reflect (~ ?b1) (~~ ?b1) *)

(* andP
     : reflect (?b1 /\ ?b2) (?b1 && ?b2) *)

(*orP
     : reflect (?b1 \/ ?b2) (?b1 || ?b2) *)
Lemma impP(p q:bool): reflect (p->q)((negb p) || q).
  Proof. { case p eqn:pH; case q eqn:qH; simpl.
       constructor. auto. 
       constructor. intro H2. cut (false=true). discriminate. apply H2. auto. 
       constructor. auto. 
       constructor. discriminate. } Qed. 
Lemma impP1(P Q:Prop)(p q:bool)(HP: reflect P p)(HQ: reflect Q q):  reflect (P->Q)((negb p) || q).
Proof. { case p eqn:pH; case q eqn:qH; simpl.
       constructor. move /HP. apply /HQ.
       constructor. intro H2. absurd (Q). move /HQ. discriminate. apply H2; apply /HP;auto.
       constructor. move /HP. discriminate.
       constructor. move /HP. discriminate. } Qed.
Lemma switch1(b:bool): b=false -> ~ b.
Proof. intros H H1.  rewrite H1 in H. discriminate H. Qed.
Lemma switch2(b:bool): ~ b -> b=false.
Proof. intros H. case b eqn:H1. absurd (true);auto. auto. Qed.

Lemma bool_fun_equal (B1 B2: bool): (B1-> B2)-> (B2-> B1)-> B1=B2.
    Proof. intros H1 H2. destruct B1; destruct B2; auto.
           replace false with true. auto. symmetry; auto. Qed.

    Hint Resolve bool_fun_equal: core.

End GeneralReflections.


Hint Immediate reflect_intro reflect_elim  reflect_EM reflect_dec dec_EM: core.
Hint Resolve idP impP impP1: core.
Hint Resolve bool_fun_equal: core.

Ltac solve_dec := eapply reflect_dec; eauto.
Ltac solve_EM  := eapply reflect_EM; eauto.

Ltac switch:=  (apply switch1||apply switch2).
Ltac switch_in H:= (apply switch1 in H || apply switch2 in H).

Ltac right_ := apply /orP; right.
Ltac left_ := apply /orP; left.
Ltac split_ := apply /andP; split.


Section NaturalNumbers.

Lemma ltP (x y:nat): reflect (x < y) (Nat.ltb x y).
Proof. { apply reflect_intro. split.
       { unfold "<".  unfold Nat.ltb. 
         revert y. induction x. intro y; case y. simpl.
         intro H. inversion H. simpl. auto.
         intro y;case y.
         intro H; inversion H. intros n H. 
         apply IHx. lia. }
       { 
         revert y. induction x. intro y; case y. simpl.
         intro H. inversion H. intros; lia.
         intro y;case y. simpl. intro H; inversion H.
         intro n. 
         intro H; apply IHx in H. lia. } } Qed.

Lemma leP (x y: nat): reflect (x <= y) (Nat.leb x y).
Proof. { apply reflect_intro. split.
       { revert y. induction x. intro y; case y; simpl; auto.
         intro y;case y.
         intro H; inversion H. intros n H. 
         apply IHx. lia.
        }
       { revert y. induction x. intro y; case y; intros; lia. 
         intro y;case y. simpl. intro H; inversion H.
         intro n.
         intro H; apply IHx in H. lia. } } Qed.

Lemma nat_reflexive: reflexive Nat.leb.
  Proof. unfold reflexive; induction x; simpl; auto. Qed.

Lemma nat_transitive: transitive Nat.leb.
Proof. unfold transitive. intros x y z h1 h2. move /leP in h1. move /leP in h2.
         apply /leP. lia. Qed.

Hint Resolve leP ltP nat_reflexive nat_transitive: core.

End NaturalNumbers.

Hint Resolve leP ltP nat_reflexive nat_transitive: core.
