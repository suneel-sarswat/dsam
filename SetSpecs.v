



(* -----------------Description --------------------------------------------------
   
   This file summarises some useful results from List Module of standard Library. 
   We create a hint database to remember important results regarding lists (hint_list).

   Some new definitions:
   Definition Empty (s:list A):Prop := forall a : A, ~ In a s.
   Definition Equal (s s': list A) := forall a : A, In a s <-> In a s'.
   Definition Subset (s s': list A) := forall a : A, In a s -> In a s'.

   Notation "s [=] t" := (Equal s t) (at level 70, no associativity).
   Notation "s [<=] t" := (Subset s t) (at level 70, no associativity).
   Notation "| s |":= (length s) (at level 70, no associativity).

  --------------------   ------------------  ------------------------------------- *)



From Coq Require Export ssreflect  ssrbool.
Require Export Lists.List Lia.

Set Implicit Arguments.

Hint Resolve in_eq in_cons in_inv in_nil in_dec: core.

Section BasicListFacts.
  Variable A:Type.
  Lemma in_inv1 : forall (a b:A) (l:list A), In b (a :: l) -> b = a \/ In b l.
  Proof. { intros  a b l H. cut (a=b \/ In b l). 
       2: {  auto. } intros H1; destruct H1 as [H1 | H2].
       left; symmetry; auto. right;auto. } Qed.
  Lemma in_inv2: forall (x a:A) (l:list A), In x (a::l)-> x <> a -> In x l.
  Proof.  { intros x a l H. cut (x=a \/ In x l). intro H1;destruct H1 as [Hl1|Hr1].
          intro;contradiction. auto. eapply in_inv1;auto. } Qed.
  Lemma in_inv3: forall (x a:A) (l:list A), In x (a::l)-> ~ In x l -> x = a.
    Proof.  { intros x a l H. cut (x=a \/ In x l). intro H1;destruct H1 as [Hl1|Hr1].
          intro;auto. intro;contradiction.  eapply in_inv1;auto. } Qed.
  Hint Resolve in_inv1 in_inv2 in_inv3 : core.
  (*---------Some facts about NoDup on a list --------------------------------*)
  Lemma nodup_intro (a:A)(l: list A): ~ In a l -> NoDup l -> NoDup (a::l).
    Proof.  intros H1 H2; eapply NoDup_cons_iff;tauto.  Qed. 
  Lemma nodup_elim1 (a:A)(l: list A): NoDup (a::l)-> NoDup (l).
  Proof. intro H. eapply NoDup_cons_iff; eauto. Qed.
  Lemma nodup_elim2 (a:A)(l: list A): NoDup (a::l) -> ~ In a l.
    Proof. intro H. eapply NoDup_cons_iff; eauto. Qed. 
  
  Hint Immediate nodup_elim1  nodup_elim2  nodup_intro : core.
  End BasicListFacts.
Hint Resolve in_inv1 in_inv2 in_inv3: core.
Hint Immediate nodup_elim1  nodup_elim2  nodup_intro : core.



Section SetSpec.
  Variable A:Type.
  Definition Empty (s:list A):Prop := forall a : A, ~ In a s.
  
  Definition Subset (s s': list A) := forall a : A, In a s -> In a s'.
  Definition Equal (s s': list A):= Subset s s' /\ Subset s' s.
  
  (* Inductive Forall (A : Type) (P : A -> Prop) : list A -> Prop := 
     | Forall_nil : Forall P nil 
     | Forall_cons : forall (x : A) (l : list A), P x -> Forall P l -> Forall P (x :: l)  *)
  
  (* Inductive Exists (A : Type) (P : A -> Prop) : list A -> Prop :=
      |Exists_cons_hd : forall (x : A) (l : list A), P x -> Exists P (x :: l) 
      | Exists_cons_tl : forall (x : A) (l : list A), Exists P l -> Exists P (x :: l) *)
  
  (* Inductive NoDup (A : Type) : list A -> Prop := 
      | NoDup_nil : NoDup nil 
      | NoDup_cons : forall (x : A) (l : list A), ~ In x l -> NoDup l -> NoDup (x :: l) *)
End SetSpec.

Ltac unfold_spec := try(unfold Equal);try(unfold Subset);try(unfold Empty).



  Notation "s [=] t" := (Equal s t) (at level 70, no associativity).
  Notation "s [<=] t" := (Subset s t) (at level 70, no associativity).
  Notation "| s |":= (length s) (at level 70, no associativity).
  

Section BasicSetFacts.
  Variable A:Type.

  (*-----------------------Subset (spec) and its properties ------------------------*)
  Lemma Subset_intro (a:A)(l s: list A): l [<=] s -> (a::l) [<=] (a::s).
  Proof. intros H x H1.  destruct H1. subst a;auto. auto. Qed.
  Lemma Subset_intro1 (a:A)(l s: list A): l [<=] s -> l [<=] (a::s).
    Proof. intros H x H1. simpl;right;auto. Qed. 
  Lemma Subset_elim1 (a:A) (s s':list A): Subset (a:: s) s'-> In a s'.
  Proof. { unfold Subset. intro H. apply H. auto. } Qed.
   Lemma Subset_elim2 (a:A) (s s':list A): Subset (a:: s) s'->  Subset s s'.
  Proof. { unfold Subset. intro H.  intros a1 H1.
           apply H. auto. } Qed.
  Lemma self_incl (l:list A): l [<=] l.
  Proof. unfold Subset; tauto.  Qed. 
  Hint Resolve self_incl: core.

  Lemma Subset_nil (l: list A): nil [<=] l.
  Proof. unfold "[<=]"; simpl; intros; contradiction. Qed.
  Lemma Subset_of_nil (l: list A): l [<=] nil -> l=nil.
    Proof. induction l. auto. intro H. absurd (In a nil); auto. Qed.

  Lemma Subset_trans (l1 l2 l3: list A): l1 [<=] l2 -> l2 [<=] l3 -> l1 [<=] l3.
  Proof. intros H H1 x Hx1. eauto. Qed. 
 Lemma Subset_elim (a1 a2: A)(l1 l2:list A):
           (a1::l1) [<=](a2::l2) -> ~In a2 l1 ->  l1 [<=] l2.
  Proof. { unfold "[<=]". intros. assert (In a (a1 :: l1));eauto.
  apply H in H2.  destruct H2. subst a. eauto. exact. } Qed.

    Lemma Subset_elim0 (a1 a2: A)(l1 l2:list A):
           (a1::l1) [<=](a2::l2) -> ~In a2 l1 ->  a1<>a2 ->
           (a1::l1) [<=] l2.
  Proof. { unfold "[<=]". intros. apply H in H2 as H2a.  destruct H2a. subst a.
   eauto. exact. } Qed.
  Lemma Subset_elim3 (a:A)(l1 l2: list A):
       l1 [<=](a::l2) -> ~In a l1 -> l1 [<=] l2.
  Proof. unfold "[<=]". intros.  apply H in H1 as H1a.
       destruct H1a. subst. eauto. auto. Qed.
   
Hint Extern 0 (?x [<=] ?z)  =>
match goal with
| H: (x [<=] ?y) |- _ => apply (@Subset_trans  x y z)
| H: (?y [<=] z) |- _ => apply (@Subset_trans  x y z)                                   
end : core.
  
  (* ---------------------- Equal (spec) and their properties--------------------*)
  Lemma Eq_refl (s: list A):  s [=] s.
  Proof.  unfold Equal. split;auto using self_incl.  Qed. 
  Lemma Eq_sym (s s':list A): s [=] s' -> s' [=] s.
  Proof. unfold Equal.  tauto. Qed. 
  Lemma Eq_trans1 ( x y z : list A) : x [=] y -> y [=] z -> x [=] z.
  Proof. { unfold Equal.  intros H H1. destruct H as [H0 H]; destruct H1 as [H1a H1].
           split; auto.  } Qed.

 Hint Extern 0 (?x [=] ?z)  =>
match goal with
| H: (x [=] ?y) |- _ => apply (@Eq_trans1  x y z)
| H: (?y [=] z) |- _ => apply (@Eq_trans1  x y z)                                   
end : core.


  Lemma Equal_intro (s s': list A): s [<=] s' -> s' [<=] s -> s [=] s'.
  Proof. unfold "[=]".  tauto. Qed.
  Lemma Equal_intro1 (s s': list A): s = s' -> Equal s s'.
  Proof. intro; subst s; apply Eq_refl; auto. Qed.
  Lemma Equal_elim ( s s': list A): s [=] s' ->  s [<=] s' /\ s' [<=] s.
  Proof. unfold_spec; unfold iff. intros H; split; intro a;apply H. Qed.

  (* ---------------- introduction and elimination for filter operation---------- *)
  (* Check filter :  forall A : Type, (A -> bool) -> list A -> list A *)
  (* Check filter_In : forall (A : Type) (f : A -> bool) (x : A) (l : list A),
       In x (filter f l) <-> In x l /\ f x = true *)
  Lemma filter_elim1 (f: A->bool)(l: list A)(x: A): In x (filter f l)-> In x l.
  Proof. apply filter_In. Qed.
  Lemma filter_elim2 (f: A->bool)(l: list A)(x: A): In x (filter f l)-> (f x).
  Proof. apply filter_In. Qed.
  Lemma filter_intro (f: A->bool)(l: list A)(x: A): In x l -> (f x)-> In x (filter f l).
  Proof. intros; apply filter_In; split;auto. Qed.

  Hint Immediate filter_elim1 filter_elim2 filter_intro: core.


 (*--------Strong Induction, Well founded induction and set cardinality ----------*)

  
Theorem strong_induction: forall P : nat -> Prop,
                    (forall n : nat, (forall k : nat, (k < n -> P k)) -> P n) ->
                    forall n : nat, P n.
Proof. { intros P Strong_IH n.
         pose (Q:= fun (n: nat)=> forall k:nat, k<= n -> P k). 
         assert (H: Q n);unfold Q. 
         { induction n. 
           { intros k H;apply Strong_IH.
             intros k0 H1.  cut (k0 < 0). intro H2; inversion H2. lia.  } 
           { intros k H0.
             assert (H1: k < (S n) \/ k = (S n) ).  lia.
             elim H1. intro. apply IHn. lia. 
             intro H. subst k. apply Strong_IH. intros. apply IHn. lia. } }
         unfold Q in H. apply H. lia. }   Qed. 

Definition lt_set (l1 l2: list A):= |l1| < |l2|.

Lemma lt_set_is_well_founded: well_founded lt_set.
Proof. { unfold well_founded. intro a.
       remember (|a|) as n. revert Heqn. revert a.
       induction n using strong_induction.
       { intros a H1. apply Acc_intro.
         intros a0 H2. apply H with (k:= |a0|).
         subst n; apply H2. auto. } } Qed.



Lemma non_zero_size (a:A)(l: list A): In a l -> |l| > 0.
  Proof. { induction l.
         { simpl; tauto. }
         { intros. simpl. lia. } } Qed.
         
Lemma non_nil_size (l: list A): |l| > 0 -> l<>nil.
  Proof. { induction l.
         { simpl. intro H. lia. }
         { intros. intro. assert (H1: In a nil).
           rewrite <- H0. auto. destruct H1. } } Qed.
           
Lemma element_list (l: list A)(a b : A): a<>b -> In b (a::l) -> In b l.
Proof. intros H1 H2. simpl in H2. destruct H2. destruct H1;auto. exact. Qed. 

Hint Resolve non_zero_size: core.  
 
End BasicSetFacts.


   
Hint Extern 0 (?x [<=] ?z)  =>
match goal with
| H: (x [<=] ?y) |- _ => apply (@Subset_trans _ x y z)
| H: (?y [<=] z) |- _ => apply (@Subset_trans _ x y z)                                   
end : core.

Hint Extern 0 (?x [=] ?z)  =>
match goal with
| H: (x [=] ?y) |- _ => apply (@Eq_trans1 _ x y z)
| H: (?y [=] z) |- _ => apply (@Eq_trans1 _ x y z)                                   
end : core.


Hint Immediate Eq_refl Eq_sym Equal_elim Equal_intro Equal_intro1: core.
Hint Immediate  Subset_elim1 Subset_elim2 Subset_nil Subset_of_nil Subset_elim3: core.
Hint Resolve  self_incl: core.
Hint Resolve Subset_intro Subset_intro1: core.

Hint Immediate filter_elim1 filter_elim2 filter_intro: core.

Hint Resolve lt_set_is_well_founded: core.

Hint Resolve non_zero_size element_list: core. 
