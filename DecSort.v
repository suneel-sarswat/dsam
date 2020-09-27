




(* ------   In this file we formalize the concept of sorting in a list.  We consider lists
   of elements (on an arbitrary type A) with a boolean comparison operator (lr: A-> A-> bool).
   Most of  the results in this file assumes only   
   1. reflexive, 
   2. transitive and 
   3. comparable 
   nature of the boolean operator lr. 
   Only the last result (equality of head) assumes the antisymmetric
   property of lr. 

   Following are the concepts formalized in this file: 

   Sorted l      <==> l is sorted w.r.t comp operator lr 
   putin a l      ==> puts the element a into a sorted list at its correct position w.r.t lr
   sort l         ==> sorts the list l w.r.t the comp operator lr 

   Some of the useful results in this file are:

   Lemma putin_correct (H_trans: transitive lr)(H_comp: comparable lr):
    forall (a:A) (l: list A), Sorted l -> Sorted (putin a l).

   Lemma nodup_putin (a:A)(l:list A): NoDup (a::l)-> NoDup (putin a l).

   Lemma sort_correct (H_trans: transitive lr)(H_comp: comparable lr):
    forall(l: list A), Sorted (sort l).

   Lemma sort_equal (l: list A): Equal l (sort l).

   Lemma nodup_sort (l: list A): NoDup l -> NoDup (sort l). ------------------  *)



Require Export Lists.List.
Require Export GenReflect SetSpecs.
Require Export Lia.

Set Implicit Arguments.

Section Sorting.
  Context {A: Type }.

  Variable lr: A->A-> bool.
  Notation " a <=r b":= (lr a b)(at level 70, no associativity).
  
 (* ------------- sorting a list of elements by lr relation ------------------------------*)
  
  Inductive  Sorted : list A-> Prop:=
  | nil_Sorted: Sorted nil
  | cons_Sorted (a:A)(l: list A): Sorted l -> (forall x, (In x l -> (a <=r x))) -> Sorted (a::l).

  Lemma Sorted_intro (a:A)(b:A)(l: list A)(Htrans: transitive lr):
    a <=r b -> Sorted (b::l)-> Sorted (a::b::l).
  Proof. { intros H H0. constructor. auto. intros x H1. destruct H1. subst x. auto.
         eapply Htrans with (y:=b). eauto. inversion H0. eauto. } Qed.


  Lemma Sorted_elim1 (a:A) (b:A) (l: list A): (Sorted (a::b::l)) -> (a <=r b).
  Proof. intro H. inversion H.  eapply H3. auto.  Qed.
  Lemma Sorted_elim4 (a:A) (l:list A): Sorted (a::l) ->(forall x, In x l -> a <=r x).
  Proof. intro H. inversion H. auto. Qed.
  Lemma Sorted_elim2 (a:A) (l:list A)(Hrefl: reflexive lr):
    Sorted (a::l) ->(forall x, In x (a::l) -> a <=r x).
  Proof. intro H. inversion H. intros. destruct H4. subst x.  eauto. eauto. Qed.
  Lemma Sorted_elim3 (a:A) (l:list A): (Sorted (a::l)) -> Sorted l.
  Proof. intro H. inversion H;auto. Qed.
  Lemma Sorted_subset (a1 a2:A) (l1 l2: list A) (Htrans: transitive lr)(Hrefl: reflexive lr):
  Sorted (a1::l1) -> Sorted (a2::l2) -> (a1::l1) [<=] (a2::l2) -> In a2 (a1::l1)
  -> (a1 <=r a2)/\a2 <=r a1.
  Proof. intros. eapply Sorted_elim2 with (a:=a1)(x:=a2) in H. assert (In a1 (a2::l2)).
  apply H1. auto. eapply Sorted_elim2 with (a:=a2)(x:=a1) in H3. auto. auto. auto.
  auto. auto. Qed.

  Lemma Sorted_single : forall a:A, (Sorted (a::nil)).
  Proof. constructor. constructor. intros;simpl;contradiction. Qed.
  
  Lemma last_in_Sorted (a d:A)(l:list A)(Htrans: transitive lr)(Hrefl: reflexive lr): 
   Sorted l -> In a l -> lr a (last l d).
  Proof. { revert a. 
         induction l as [|b1 l']. 
         { intros a H H0. simpl in H0. auto. }
         { intros a0 H H0. 
           destruct H0.
           { subst b1.
           case l' as [|b2 l''] eqn: H1.
           { simpl. auto. }
           { replace (last (a0 :: b2 :: l'') d) with (last (b2 :: l'') d). 
             assert (H2: b2 <=r (last (b2 :: l'') d)). 
             { apply IHl'. eapply Sorted_elim3. exact H. auto. }
             assert (H3: a0 <=r b2). 
             { eapply Sorted_elim1. exact H. }
             eauto. 
             simpl. destruct l'';auto. } }
            { case l' as [|b2 l''] eqn: H1.
             { destruct H0. }
             { replace (last (b1 :: b2 :: l'') d) with (last (b2 :: l'') d). 
             apply IHl'. eapply Sorted_elim3. exact H. auto. 
             simpl. destruct l'';auto. } } } } Qed.


  Hint Resolve Sorted_elim1 Sorted_elim2 Sorted_elim3 Sorted_elim4
       Sorted_single Sorted_intro last_in_Sorted : core.

     
  Fixpoint putin (a: A) (l: list A) : list A:=
    match l with
    |nil=> a::nil
    |b::l1 => match a <=r b with
             |true => a::l
             |false => b::(putin a l1)
                    end
    end.

  Lemma putin_intro (a:A) (l: list A): forall x, In x l -> In x (putin a l).
  Proof. { intros x H. induction l. simpl in H. contradiction. simpl.
           destruct ( a <=r a0). destruct H. subst x. all: auto.  destruct H. subst x; auto.
          apply IHl in H as H1;auto.  } Qed.
         
  Lemma putin_intro1 (a:A) (l: list A): In a (putin a l).
  Proof. { induction l. simpl. tauto. simpl. destruct ( a <=r a0). all: auto.  } Qed.

  Lemma putin_elim (a:A) (l: list A): forall x, In x (putin a l) -> (x=a)\/(In x l).
  Proof. { intros x H. induction l. simpl in H. simpl. destruct H. left. auto. auto.
           simpl in H. destruct ( a <=r a0).   destruct H. auto. auto. destruct H.
           right;subst x;auto. apply IHl in H as H2. destruct H2. auto. right. auto.  } Qed.
   
  Definition comparable (lr: A->A-> bool) := forall x y, lr x y=false -> lr y x.
 
  Lemma putin_correct (H_trans: transitive lr)(H_comp: comparable lr):
    forall (a:A) (l: list A), Sorted l -> Sorted (putin a l).
  Proof. { intros a l. revert a.  induction l.
         { intros a1 H.  simpl. apply Sorted_single. }
           simpl. intros a1 H.  destruct ( a1 <=r a) eqn:H0.
         {  auto.  }
         { cut ( a <=r a1 = true).
           intro H1.  constructor. eauto. 
           intros x H2. apply putin_elim in H2 as H3. destruct H3.
           subst x;auto. eauto.  apply H_comp. eauto. } } Qed.
  
  Lemma nodup_putin (a:A)(l:list A): NoDup (a::l)-> NoDup (putin a l).
  Proof.  { revert a. induction l.
          { simpl. auto. }
          { intros a0 H. assert (Ha: NoDup (a::l)).  eauto. 
            simpl. destruct (a0 <=r a) eqn: H1. auto.
            constructor.
            { intro H2. assert ( H2a: a=a0 \/ In a l). eauto using putin_elim.
              destruct H2a. subst a. inversion H. eauto.  inversion Ha; contradiction. }
            apply IHl. inversion H. constructor; eauto.  } } Qed.

  Lemma putin_card (a:A)(l: list A): | putin a l | = S (|l|).
  Proof. { induction l.
         { simpl;auto. }
         { simpl. case (a <=r a0) eqn:H.
           simpl; auto. simpl; rewrite IHl; auto. } } Qed.
  
  
  Hint Resolve putin_intro putin_intro1 putin_elim putin_correct nodup_putin: core.


   Fixpoint sort (l: list A): list A:=
    match l with
    |nil => nil
    |a::l1 => putin a (sort l1)
    end.
  
  
  Lemma sort_intro (l: list A): forall x, In x l -> In x (sort l).
  Proof. { intros x H. induction l. eauto. simpl. destruct H. subst x.
         apply putin_intro1. eauto using putin_intro. } Qed.

  Lemma sort_elim (l: list A): forall x, In x (sort l) -> In x l.
  Proof. { intros x H. induction l. simpl in H. contradiction.
         simpl in H. apply putin_elim in H. destruct H. subst x;eauto. eauto. } Qed.

  Lemma sort_correct (H_trans: transitive lr)(H_comp: comparable lr):
    forall(l: list A), Sorted (sort l).
  Proof. induction l. simpl. constructor. simpl. eauto using putin_correct. Qed.

  Hint Resolve sort_elim sort_intro sort_correct: core.
  
  Lemma sort_equal (l: list A): Equal l (sort l).
  Proof. split;intro; eauto. Qed.

   Lemma sort_equal1 (l: list A): Equal (sort l) l.
  Proof. split;intro; eauto. Qed.

  Lemma sort_same_size (l: list A): |sort l| = |l|.
  Proof. { induction l.
         { simpl;auto. }
         { simpl. replace (|putin a (sort l)|) with (S(|sort l|)).
           rewrite IHl. auto. symmetry. apply putin_card. } } Qed.

  Lemma Sorted_equal (l l': list A): Equal l l' -> Equal l (sort l').
  Proof. intro. cut (Equal l' (sort l')). eauto.  apply sort_equal. Qed.
  Lemma Sorted_equal1(l l': list A): Equal l l' -> Equal (sort l) l'.
  Proof. intro. cut (Equal l (sort l)). eauto. apply sort_equal. Qed.

  Lemma nodup_sort (l: list A): NoDup l -> NoDup (sort l).
  Proof. { induction l. eauto.
         {  simpl. intro H.  cut (NoDup (a::sort l)). eauto.
            constructor.
            { intro H1. absurd (In a l). inversion H; auto. eapply  sort_equal;auto. }
            eauto. } } Qed.

  (*--upto this point only reflexive, transitive and comparable property of <=r is needed--- *)

 
  (* ---------------------head in Sorted lists l and l'-------------------------- *)

   Definition empty: list A:= nil.
  
  Lemma empty_equal_nil_l (l: list A): l [=] empty -> l = empty.
  Proof. { case l. auto. intros s l0. unfold "[=]". intro H. 
           destruct H as [H1 H2]. absurd (In s empty). all: eauto. } Qed.


  
   (*-------- antisymmetric requirement is only needed in the following lemma--------*)
  Lemma head_equal_l (a b: A)(l s: list A)(Href: reflexive lr)(Hanti: antisymmetric lr):
    Sorted (a::l)-> Sorted (b::s)-> Equal (a::l) (b::s)-> a=b.
  Proof. { intros H H1 H2. 
         assert(H3: In b (a::l)).
         unfold "[=]" in H2. apply H2. auto.
         assert (H3A: a <=r b). eapply Sorted_elim2;eauto.
         assert(H4: In a (b::s)).
         unfold "[=]" in H2. apply H2. auto.
         assert (H4A: b <=r a). eapply Sorted_elim2;eauto.
         eapply Hanti. split_;auto. } Qed.  

End Sorting. 


Hint Resolve Sorted_elim1 Sorted_elim2 Sorted_elim3 Sorted_elim4
     Sorted_single Sorted_intro last_in_Sorted : core.
Hint Resolve putin_intro putin_intro1 putin_elim putin_correct nodup_putin : core.
Hint Resolve sort_elim sort_intro sort_correct sort_same_size : core.
Hint Resolve sort_equal sort_equal1 Sorted_equal Sorted_equal1 nodup_sort: core.
Hint Resolve empty_equal_nil_l head_equal_l: core.




(*
 Definition l := 12::42::12::11::20::0::3::30::20::0::nil.
 Eval compute in (sort (fun x y => Nat.ltb y x) l).
 Eval compute in (sort (fun x y => ~~ (Nat.ltb x y)) l).
*)
 

