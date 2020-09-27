


(* ------ This file contains results about minimum and maximum value in a list of elements 
   of an arbitrary type (A: Type) with a boolean comparison operator (lr: A-> A-> bool).
   

  The results in this file are prooved under the following three assumptions
  on the comparison operator lr:

  Hypothesis lr_refl : reflexive lr.      (*  forall x : A, lr x x *)
  Hypothesis lr_trans: transitive lr.     (*  forall y x z : A, lr x y -> lr y z -> lr x z *) 
  Hypothesis lr_comparable: comparable lr.    (*  forall x y : A, lr x y=false -> lr y x   *)
  
  Functions defined are: 
  maxof a b   => returns maximum among a and b
  maxin l d   => returns the maximum value in the list l (returns d if l is nil) 
  minof a b   => returns minimum among a and b
  minin l d   => returns the minimum value in the list l (returns d if l is nil) 

 Furthermore, we also prove some results about the existence of min and maximum the list l
 with respect to the lr relation as well as min and max with property P.

 Lemma min_exists (l: list A):
                       l<>nil -> exists min, In min l /\ (forall x, In x l -> min <=r x).

 Lemma max_exists (l: list A): 
                       l<>nil -> exists max, In max l /\ (forall x, In x l -> x <=r max).

 Lemma min_withP_exists (l: list A)(P: A->bool): (exists a, In a l /\ P a) -> 
                (exists min, In min l /\ P min /\ (forall x, In x l -> P x -> min <=r x)).

 Lemma max_withP_exists (l: list A)(P: A->bool): (exists a, In a l /\ P a) -> 
                (exists max, In max l /\ P max /\ (forall x, In x l -> P x -> x <=r max)).
  
 ---------------------------------------------------------------------------------------- *)


Require Export Lists.List.
Require Export GenReflect SetSpecs.
Require Export Lia.


Set Implicit Arguments.

Section Min_Max.

  Context {A: Type }.

  Variable lr: A->A-> bool.
  Notation " a <=r b":= (lr a b)(at level 70, no associativity).
  Definition comparable (lr: A->A-> bool) := forall x y, lr x y=false -> lr y x.
  
 (*-----------Partial functions on lists ( maxin and minin ) ---------------------------  *)

  
  Definition maxof (a b :A): A := match a <=r b with
                                  |true => b
                                  |false => a           
                                  end.


  (* reflexive: forall x : T, R x x *)
  
  Hypothesis lr_refl : reflexive lr.
  
  Hypothesis lr_trans: transitive lr.
  Hypothesis lr_comparable: comparable lr.
  
  
  Lemma maxof_spec1 (a b: A): a <=r maxof a b.
  Proof. unfold maxof. destruct (a <=r b) eqn:H; eauto using lr_refl. Qed. (* refl *)
  Lemma maxof_spec2 (a b: A): b <=r maxof a b. 
  Proof. unfold maxof. destruct (a <=r b) eqn:H; eauto. Qed. (* refl and comparable *)
  Lemma maxof_spec3 (a b c:A): c <=r a -> c <=r maxof a b.
  Proof.  unfold maxof. destruct (a <=r b) eqn:H. all: try tauto. intro; eauto. Qed.
  Lemma maxof_spec4 (a b c:A): c <=r b -> c <=r maxof a b.
  Proof. unfold maxof. destruct (a <=r b) eqn:H. all: try tauto. intro; eauto. Qed.
  Lemma maxof_spec5 (a b: A): a=maxof a b \/b=maxof a b.
  Proof. unfold maxof. destruct (a <=r b). right. auto. left. auto.
  Qed.

  Hint Resolve maxof_spec1 maxof_spec2 maxof_spec3 maxof_spec4 maxof_spec5: core.
  
   Fixpoint maxin (l: list A)(d: A): A:=
    match l with
    |nil => d
    |a::l' => maxof a (maxin l' a)  
    end.

   Lemma maxin_elim (l: list A)(a d:A): maxin (a::l) d = maxin (a::l) a.
   Proof. simpl; auto. Qed.

   Lemma maxin_elim1 (a:A) (l:list A) (d:A) : In (maxin (a::l) d) (a::l).
   Proof.  { revert a. revert d. induction l.
            { simpl. intros; left.
              unfold maxof. replace (a <=r a) with true. auto. symmetry;apply lr_refl. }
            { intros d a0. replace (maxin (a0 :: a :: l) d) with (maxof a0 (maxin (a::l) a0)).
              unfold maxof.
              destruct (a0 <=r maxin (a :: l) a0) eqn:H; eauto.
              simpl;auto.  } } Qed.

Lemma maxin_elim2 (l:list A) (d:A) :l<>nil -> In (maxin l d) l.
   Proof. { revert d. induction l. intros. destruct H. auto. intros. eapply maxin_elim1. } Qed.
   
         

 Lemma maxin_spec (l:list A)(d:A)(a:A): In a l -> (a <=r (maxin l d)).
   Proof. { generalize d. induction l.
          { intros d0 H. inversion H. }
          { intros d0 H. simpl. destruct H.
            { subst a; eauto. } apply maxof_spec4. apply IHl. exact H. } } Qed.     
 
  Lemma maxin_spec0 (l:list A)(d:A)(a:A): In (maxin l d) l -> ((maxin l d) <=r (maxin (a::l) d)).
   Proof. { generalize d. induction l.
          { intros d0 H. simpl in H.  inversion H. }
          { intros d0 H. simpl. destruct H. auto.
            apply maxin_spec with (a:=maxof a0 (maxin l a0))(l:=(a::a0::l))(d:=d0).
             simpl in H. auto. } } Qed.     
 
   Hint Resolve maxin_spec maxin_spec0 maxin_elim maxin_elim1: core.

    Definition minof (a b :A): A:= match a <=r b with
                                  |true => a
                                  |false => b
                                   end.
    
    Lemma minof_spec1 (a b: A): minof a b <=r a.
     Proof. unfold minof. destruct (a <=r b) eqn:H; eauto. Qed.
   
   Lemma minof_spec2 (a b: A): minof a b <=r b.
   Proof. unfold minof. destruct (a <=r b) eqn:H; eauto. Qed.

   Lemma minof_spec3 (a b c:A): a <=r c -> minof a b <=r c.
   Proof. unfold minof. destruct (a <=r b) eqn:H. all: try tauto. intro; eauto. Qed.  
   Lemma minof_spec4 (a b c:A): b <=r c ->  minof a b <=r c.
   Proof. unfold minof. destruct (a <=r b) eqn:H. all: try tauto. intro; eauto. Qed. 
   Lemma minof_spec5 (a b: A): a=minof a b \/b=minof a b.
  Proof. unfold minof. destruct (a <=r b). left. auto. right. auto.
  Qed.

   Hint Resolve minof_spec1 minof_spec2 minof_spec3 minof_spec4 minof_spec5: core.

   Fixpoint minin (l: list A)(d: A): A:=
    match l with
    |nil => d
    |a::l' => minof a (minin l' a)
    end.

   Lemma minin_elim (l: list A)(a d:A): minin (a::l) d = minin (a::l) a.
   Proof. simpl; auto. Qed.

   Lemma minin_elim1 (a:A) (l:list A) (d:A) : In (minin (a::l) d) (a::l).
   Proof.  { revert a. revert d. induction l.
            { simpl. intros; left.
              unfold minof. replace (a <=r a) with true. auto. symmetry;apply lr_refl. }
            { intros d a0. replace (minin (a0 :: a :: l) d) with (minof a0 (minin (a::l) a0)).
              unfold minof.
              destruct (a0 <=r minin (a :: l) a0) eqn:H; eauto.
              simpl;auto. } } Qed.
              
Lemma minin_elim2 (l:list A) (d:A) :l<>nil -> In (minin l d) l.
   Proof. { revert d. induction l. intros. destruct H. auto.
        { case l eqn: Hl. simpl. left. unfold minof. destruct (a <=r a). auto. auto.
        intros. rewrite <- Hl. rewrite <- Hl in IHl.
        assert (l<>nil). subst. assert (| a0::l0|>0). simpl. 
        lia. apply non_nil_size.  exact.  apply IHl with (d:=a) in H0.
        simpl. assert (a=minof a (minin l a) \/ (minin l a)=minof a (minin l a)).
        eapply minof_spec5. destruct H1. left. exact. right.
        rewrite <- H1. exact. } }Qed.
        
   Lemma minin_spec (l:list A)(d:A)(a:A): In a l -> ((minin l d) <=r a).
   Proof. { generalize d. induction l.
          { intros d0 H. inversion H. }
          { intros d0 H. simpl. destruct H.
            { subst a; eauto. } apply minof_spec4. apply IHl. exact H. } } Qed.

     Lemma minin_spec0 (l:list A)(d:A)(a:A): In (minin l d) l -> ((minin (a::l) d) <=r (minin l d)).
   Proof. { generalize d. induction l.
          { intros d0 H. simpl in H.  inversion H. }
          { intros d0 H. simpl. destruct H. auto. 
            apply minin_spec with (a:=minof a0 (minin l a0))(l:=(a::a0::l))(d:=d0).
             simpl in H. auto. } } Qed.     
 
   Hint Resolve minin_spec minin_spec0 minin_elim minin_elim1: core.

   (*---------------- Existence of Minimum and Maximum in the non-empty list------------- *)

   Lemma min_exists (l: list A): l<>nil -> exists min, In min l /\ (forall x, In x l -> min <=r x).
   Proof. intro H. case l eqn:H1. destruct H;auto.
          exists (minin (a::l0) a). split. auto. intro x. auto. Qed.
          
   Lemma max_exists (l: list A): l<>nil -> exists max, In max l /\ (forall x, In x l -> x <=r max).
   Proof.  intro H. case l eqn:H1. destruct H;auto.
           exists (maxin (a::l0) a). split. auto. intro x. auto. Qed.
   Lemma min_withP_exists (l: list A)(P: A->bool):
     (exists a, In a l /\ P a) -> (exists min, In min l /\ P min /\ (forall x, In x l -> P x -> min <=r x)).
   Proof. { intro H.
          assert (Hl: l <> nil).
          { destruct H as [a H]. destruct H as [H H0]. intro H1.
            subst l. inversion H.  }
          set (lP:= filter P l).
          assert (HlP: lP <> nil).
          { destruct H as [a H]. destruct H as [H H0]. intro H1.
            absurd (In a lP). rewrite H1. auto.  unfold lP. auto. }
          destruct (lP) eqn: HP. destruct HlP;auto.
          exists (minin (a::l0) a). split. 
          { cut  (In (minin (a :: l0) a) lP). unfold lP;eauto.
            rewrite HP. auto. } split.
          { rewrite <- HP. cut (In (minin lP a) (lP)).
            eauto. rewrite HP. auto. }
          { intros x H1 H2. assert (H3: In x (filter P l) ). auto.
            rewrite <-HP. unfold lP. auto. } } Qed.
   Lemma max_withP_exists (l: list A)(P: A->bool):
     (exists a, In a l /\ P a) -> (exists max, In max l /\ P max /\ (forall x, In x l -> P x -> x <=r max)).
   Proof. { intro H.
          assert (Hl: l <> nil).
          { destruct H as [a H]. destruct H as [H H0]. intro H1.
            subst l. inversion H.  }
          set (lP:= filter P l).
          assert (HlP: lP <> nil).
          { destruct H as [a H]. destruct H as [H H0]. intro H1.
            absurd (In a lP). rewrite H1. auto.  unfold lP. auto. }
          destruct (lP) eqn: HP. destruct HlP;auto.
          exists (maxin (a::l0) a). split. 
          { cut  (In (maxin (a :: l0) a) lP). unfold lP;eauto.
            rewrite HP. auto. } split.
          { rewrite <- HP. cut (In (maxin lP a) (lP)).
            eauto. rewrite HP. auto. }
          { intros x H1 H2. assert (H3: In x (filter P l) ). auto.
            rewrite <-HP. unfold lP. auto. } } Qed.
          
End Min_Max.


Hint Resolve maxof_spec1 maxof_spec2 maxof_spec3 maxof_spec4: core.
Hint Resolve maxin_spec maxin_elim maxin_elim1: core.
Hint Resolve minof_spec1 minof_spec2 minof_spec3 minof_spec4: core.
Hint Resolve minin_spec minin_elim minin_elim1: core.

Hint Immediate min_exists max_exists min_withP_exists max_withP_exists: core.



Section Nat_numbers.

 Lemma nat_comparable: comparable Nat.leb.
  Proof. unfold comparable. intros x y h1. move /leP in h1. apply /leP. lia. Qed.
  
End Nat_numbers.

Hint Resolve nat_comparable: core.
