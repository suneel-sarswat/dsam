



Require Export Lists.List.
Require Export GenReflect SetSpecs.
Require Export DecSort MinMax.
Require Export DecType SetReflect.
Require Export DecList.



Set Implicit Arguments.



Section MoreDecList.

Context { A: eqType}.
(*------------------ Uniform list -----------------------------------------------------*)
  
Inductive uniform : list A -> Prop:=
| Nil_uni: uniform nil
|Sing_uni(a:A): uniform (a::nil)
|Ind_uni(a b:A)(l:list A): a=b -> uniform (b::l)-> uniform (a::b::l).

Lemma uniform_elim (a:A)(l: list A): uniform (a::l)-> (forall x, In x l -> x=a).
Proof. { revert l. induction l. 
       { simpl. intros H0 fA f. destruct f. }
       { simpl. intros H fA. inversion H. intro H5.  destruct H5 as [H5| H6].
        subst fA. symmetry. exact. apply IHl in H6. exact. subst a. exact. } } Qed. 


Lemma uniform_elim1 (a:A)(l: list A): uniform (a::l)-> (forall x, In x (a::l)-> x=a).
Proof. { induction l. 
        { simpl. intros. destruct H0. auto. inversion H0. }
        { intros. inversion H. subst a0.  simpl in H0. destruct H0. 
        auto. apply IHl. exact. simpl. exact. } } Qed.

Lemma uniform_elim2 (a:A) (l: list A): uniform (a::l)-> uniform l.
Proof. intro H. inversion H. constructor. exact. Qed.

Lemma uniform_elim4 (a1 a2:A) (l: list A) : uniform l -> In a1 l -> In a2 l -> a1=a2.
Proof. { induction l.
         { simpl. intros H1 H2. destruct H2. }
         { intros H1 H2 H3.
           assert (H0:(forall x, In x (a::l)-> x=a)).
           apply uniform_elim1. exact. specialize (H0 a1) as Ha1.
           apply Ha1 in H2. specialize (H0 a2) as Ha2.
           apply Ha2 in H3. subst a1. subst a2. auto. }} Qed.
      

Lemma uniform_elim3 (a:A) (l:list A): uniform l -> uniform (delete a l).
Proof. { revert a. 
         induction l. 
         { simpl. auto. }
         { intros.  
           case l eqn:H0. 
           { simpl. destruct (a0==a) eqn: Ha. constructor. constructor. }
           { simpl. destruct (a0==a) eqn: Ha. eapply uniform_elim2.
             exact H.
           { apply uniform_elim2 in H as H1.  specialize (IHl a0) as Hl.
             apply Hl in H1. 
             destruct (a0 == e) eqn:Hae.
             {  move /eqP in Ha.  move /eqP in Hae.  assert (H2: a<> e).
                intro. subst a0. auto. 
                apply uniform_elim4 with (a1:=a) (a2:=e) in H. subst a. 
                destruct H2. all:auto. }
             {  apply uniform_elim4 with (a1:=a) (a2:=e) in H.
                subst a. constructor. auto. simpl in H1. 
                rewrite Hae in H1. all:auto.  }}}}} Qed.

Lemma uniform_intro (a:A)(l: list A): (forall x, In x l -> x=a) -> uniform (a::l).
Proof. { intros. induction l. 
         { simpl. intros. constructor. }
         { simpl. intros.  assert (H1: (forall x : A, In x l -> x = a)).
           auto. specialize (H a0) as Ha0. assert (H2: In a0 (a0 :: l)).
           auto. apply Ha0 in H2. subst a0. apply IHl in H1.
           constructor. auto. exact. }} Qed.

(* ----------------- delete_all operation ---------------------------------------------  *)

Fixpoint del_all (a:A)(l: list A): list A:=
    match l with
    |nil => nil
    | a1::l1 => match  (a == a1) with
               |true => del_all a l1
               |false => a1 :: del_all a l1
               end
    end.

(* This function deletes all occurences of a in the list l *)

  Lemma del_all_elim1 (a b:A)(l: list A): In a (del_all b l)-> In a l.
  Proof. { induction l. 
          { simpl. auto. }
          { simpl. destruct (a==a0) eqn:H0. intros. left. move /eqP in H0.
            auto. destruct (b==a0) eqn:H1. intros. right. apply IHl in H.
            exact. simpl. intros H2. destruct H2. left. exact.
            right. apply IHl in H. exact. } } Qed.
  
  Lemma del_all_elim2 (a b:A)(l: list A): In a (del_all b l)-> (a<>b).
  Proof. { induction l. 
          { simpl. auto. }
          { simpl. destruct (b==a0) eqn:H0. exact. simpl. intros H1.
            destruct H1.  move /eqP in H0. subst a0. auto. 
            apply IHl in H. exact. } } Qed.

  Lemma del_all_intro (a b: A)(l:list A): In a l -> a<>b -> In a (del_all b l).
  Proof. { induction l. 
          { simpl. auto. } 
          { simpl. intros H1 H2. destruct H1. destruct (b==a0) eqn: H3.
            move /eqP in H3. subst a0. subst b. apply IHl in H2. exact. tauto.
            simpl. left. auto. destruct (b==a0) eqn: H4. apply IHl in H2.
            exact. exact. simpl. right. apply IHl in H2. exact. exact. }} Qed.
  
  
  Lemma del_all_iff (a b:A)(l: list A): (In a (del_all b l) <-> (In a l /\ a<>b)).
  Proof. { induction l. 
          { simpl. split. auto.  intros H. destruct H. auto. }
          { simpl. destruct (b==a0) eqn: H0. split. intros. split. right.
           apply IHl in H. destruct H. exact. apply IHl in H. destruct H.
           auto. intros H. destruct H. destruct H. move /eqP in H0. subst
           a0. subst b. tauto. apply IHl. split. exact. exact. simpl. split.
           intros H. destruct  H. split. left. auto. move /eqP in H0. 
           subst a0. auto. split. apply IHl in H. destruct H. right. exact.
           apply IHl in H. destruct H. exact. simpl. intros. destruct H.
           destruct H. left. exact.  assert (H2: (In a l) /\ (a<>b)). split.
           exact. exact.  apply IHl in H2. right. exact. } } Qed. 


  Hint Resolve del_all_elim1 del_all_elim2 del_all_intro: core.
  
  Lemma del_all_nodup (a:A)(l: list A): NoDup l -> NoDup (del_all a l).
  Proof. { induction l. 
          { simpl. auto. }
          { simpl. intros H. destruct (a==a0) eqn: H1. move /eqP in H1.
            subst a0. eauto. assert (H0:NoDup l). eauto. apply IHl in H0.
            assert (H2: ~(In a0 l)). eauto. 
            assert (H3: ~(In a0 (del_all a l))). eauto. eauto. } } Qed.

  Hint Resolve del_all_nodup: core.

 (* ------- count of an element a in the list l ----------------------------------------*)

 Fixpoint count (a:A) (l:list A) : nat:= match l with
                          | nil => 0
                          |a1::l1 => match a == a1 with
                                    |true => S (count a l1)
                                    |false => count a l1
                                    end
                                        end.
  Lemma countP1 (a:A) (l:list A): In a l -> (count a l >= 1).
  Proof. { induction l. 
          { intros H. inversion H. }
          { intros H. simpl in H. destruct H. subst a0. simpl. 
           destruct (a==a) eqn:H0. lia. move /eqP in H0. absurd (a=a).
           exact. exact. apply IHl in H. simpl. destruct (a==a0) eqn:H0.
           lia. exact. } } Qed.
  Lemma countP1b (a:A) (l:list A): (count a l >= 1) -> In a l.
  Proof. { induction l. 
          { intros H. inversion H. }
          { intros H. simpl in H.
           simpl. 
           destruct (a==a) eqn:H0. 
           destruct (a == a0) eqn: Ha.  
           left. move /eqP in Ha. auto. right.
           apply IHl in H. exact.
           destruct (a == a0) eqn: Ha. 
           left. move /eqP in Ha. auto. right. 
           apply IHl in H. exact. } } Qed.  
  
  Lemma countP2 (a:A)(l: list A): ~ In a l -> (count a l = 0).
  Proof. { intros. induction l. 
          { simpl. auto. }
          { simpl. destruct (a==a0) eqn: H0. move /eqP in H0. subst a0. 
           simpl in H. destruct H. left. exact. move /eqP in H0. 
           assert (H1: ~(In a l)). eauto. apply IHl in H1. exact. } } Qed. 
  
  Lemma countP3 (a:A)(l: list A): (count a l = 0) -> ~ In a l.
  Proof. { induction l. 
          { simpl. auto. } 
          { simpl. destruct (a==a0) eqn:H0. intros. lia. intros. 
            apply IHl in H. move /eqP in H0. intro.  destruct H1. auto.
            eauto. } } Qed. 
  
  Lemma countP4 (a:A)(l: list A): count a (a::l) = S (count a l).
  Proof. simpl. destruct (a==a) eqn:H. exact. move /eqP in H. auto. Qed.
  
  Lemma countP5 (a b:A)(l: list A): (count a l) <= count a (b::l).
  Proof. { induction l. 
         { simpl. lia. } 
         { simpl. destruct (a==a0) eqn:H0. destruct (a==b) eqn:H1. lia.
           lia. destruct (a==b) eqn: H1. lia. lia. } } Qed.
 
  Lemma countP6 (a: A)(l: list A): count a l <= |l|.
  Proof. { induction l. simpl. lia. simpl. destruct (a==a0) eqn:H0.
  lia. lia. } Qed.
  
  Lemma countP7 (a:A) (l:list A): In a l -> count a l = S(count a (delete a l)).
  Proof. { induction l. 
          { simpl. auto. }
          { simpl. intro H. destruct H as [H1 | H2]. destruct (a==a0) eqn: H0.
            exact. move /eqP in H0. auto. destruct (a==a0) eqn: H0. exact.
            apply IHl in H2. move /eqP in H0. simpl. destruct (a==a0) eqn: H1.
            move /eqP in H1. auto. exact. } } Qed.
 
  Lemma countP8 (a:A) (l:list A): forall x, x<>a-> count x (a::l) = count x l.
  Proof. { induction l. 
          { simpl. intros. destruct (x==a) eqn: H0. move /eqP in H0. auto. 
           exact. } 
          { intros. simpl. destruct (x==a) eqn:H0. move /eqP in H0. auto.
            destruct (x==a0) eqn: H1. exact. exact. }} Qed.
  
  
  Lemma countP9 (a:A) (l:list A): forall x, x<>a -> count x l = count x (delete a l).
  Proof. { induction l. 
          { simpl. intros;auto. }
          { intros. simpl. destruct (x==a0) eqn: H0. destruct (a==a0) eqn:H1.
            move /eqP in H0. move /eqP in H1. subst a0. auto. simpl. 
            destruct (x==a0) eqn: H2. auto. auto. destruct (a==a0) eqn:H2. 
            exact. simpl. destruct (x==a0) eqn: H3. inversion H0. auto. }}  Qed.
  
  Lemma countP10 (a:A)(l s:list A): count a l <= count a s -> count a (a::l) <= count a (a::s).
  Proof. { induction l. 
          { simpl. intros. destruct (a==a) eqn: H1. lia. lia. }
          { simpl. intros. destruct (a==a0) eqn:H1. destruct (a==a) eqn:H2.
            lia. lia. destruct (a==a) eqn: H2. lia. lia. } } Qed. 
  
  Lemma countP11 (a:A)(l s: list A): count a l = count a s -> count a (a::l) = count a (a::s).
  Proof. { induction l. 
          { simpl. intros. destruct (a==a) eqn: H1. auto. exact. }
           { simpl. destruct (a==a0) eqn:H1. intros. destruct (a==a) eqn:H2.
            lia. lia. destruct (a==a) eqn: H2. intros. lia. lia. }} Qed.
  
  Lemma countP12 (a:A)(l s: list A): count a l < count a s -> count a (a::l) < count a (a::s).
  Proof. {  induction l. 
          { simpl. intros. destruct (a==a) eqn: H1. lia. exact. }
          { simpl. destruct (a==a0) eqn: H2. destruct (a==a) eqn: H1. intros.
            lia. intros. lia. destruct (a==a) eqn: H1. intros. lia.
            intros. lia. }} Qed.
  
  Lemma count_nodup (l:list A): (forall x, In x l -> count x l <=1)-> NoDup l.
  Proof. { intros H.
         induction l. 
         { auto. }
         { cut (NoDup l). cut (~In a l). auto. intros H1.
          specialize (H a) as H2. 
          assert (H3:  count a (a :: l) <= 1). apply H2. auto.
          simpl in H3. replace (a==a) with true in H3.
          inversion H3. absurd (In a l). apply countP3. auto.
          exact. inversion H4. auto.
          apply IHl. intros x H1.
          cut ( count x l <= count x (a::l)).
          intros H2.
          assert (H3: count x (a :: l) <= 1).
          { apply H. auto. }
          lia. apply countP5. }} Qed.
           
  Lemma nodup_count (l:list A) (x:A): NoDup l -> In x l -> count x l <=1.
  Proof. { intros H1 H2.
           induction l. simpl. auto.
           { simpl in H2. destruct H2. 
             { subst x.
             simpl. replace (a==a) with true.
             cut (count a l =0). lia.
             cut (~In a l). eapply countP2. auto. auto. }
             { assert (Ha: x<>a). 
               { intro H2. subst x. absurd (In a l);auto. }
              replace (count x (a::l)) with (count x l).
              apply IHl. eauto. exact. symmetry.
               apply countP8. exact. }}} Qed. 
  
  Hint Immediate countP1 countP2 countP3: core.
  Hint Resolve countP4 countP5 countP6 countP7 countP8 countP9: core.
  Hint Immediate count_nodup nodup_count: core.
 
End MoreDecList.

 Hint Resolve del_all_elim1 del_all_elim2 del_all_intro: core.
 Hint Resolve del_all_nodup: core.

 Hint Immediate countP1 countP2 countP3: core.
 Hint Resolve countP4 countP5 countP6 countP7 countP8 countP9:  core.
 Hint Resolve countP10 countP11 countP12: core.
 Hint Immediate count_nodup nodup_count: core.

Section Permutation.

  Context { A: eqType }.
  
   Lemma EM:forall x y : A, x=y \/ x<>y.
   Proof. eauto. Qed.
   
   Definition empty: list A:= nil.

   Lemma count_in_putin1 (a: A)(l: list A)(lr: A-> A-> bool):
     count a (putin lr a l)= S (count a l).
   Proof. { induction l. simpl. destruct (a==a) eqn:H. auto. conflict_eq. 
           { simpl. case (lr a a0) eqn: H0.
             { destruct (a==a0) eqn:H1. move /eqP in H1.
               subst a0. assert (H: count a (a::a::l)=S(count a (a::l))). eauto.
               rewrite H. eauto.
               assert (H: count a (a :: a0 :: l) = S (count a (a0::l))).
               eauto.  move /eqP in H1. rewrite H. eauto. }
             { simpl. destruct (a==a0) eqn:H1. lia. auto. } } } Qed.
   
   Lemma count_in_putin2 (a b: A)(l: list A)(lr: A-> A-> bool):
     a<>b -> count a l = count a (putin lr b l).
   Proof. { induction l.
            { simpl; destruct (a==b) eqn:H. intros;conflict_eq. auto. }
            { intros.  simpl. case (lr b a0) eqn: H0.
              { destruct (a==a0) eqn:H1.
                move /eqP in H1. subst a0.
                replace (count a (b :: a :: l)) with (count a (a :: l)).
                eauto. symmetry; auto. move /eqP in H1.
                replace (count a (b :: a0 :: l)) with (count a (a0 :: l)).
                all: symmetry;eauto. }
              { destruct (a==a0) eqn: H1.
                move /eqP in H1. subst a0.
                replace (count a (a :: putin lr b l)) with (S(count a (putin lr b l))).
                 eauto. symmetry. auto. 
                replace (count a (a0 :: putin lr b l)) with (count a (putin lr b l)).
                auto. move /eqP in H1. symmetry;auto. }  } } Qed.
   
  Lemma count_in_sorted (a: A)(l: list A)(lr: A-> A-> bool): count a l = count a (sort lr l). 
  Proof. { induction l. simpl; auto.
           simpl. destruct  (a == a0) eqn:H0.
           move /eqP in H0. subst a.
           rewrite IHl. symmetry; apply count_in_putin1.
           move /eqP in H0. rewrite IHl.  apply count_in_putin2. auto. }  Qed.


  Hint Resolve count_in_putin1 count_in_putin2 count_in_sorted: core.
  
  (* ---------------  sublist of a list (subsequence)------------------------------------ *)

  Fixpoint sublist (l s: list A): bool := match (l, s) with
                                              |(nil , _) => true
                                              |(a::l1, nil) => false
                                              |(a::l1, b::s1) => match (a == b) with
                                                          |true => sublist l1 s1
                                                          |false => sublist l s1
                                                          end
                                       end.
  
  Lemma sublist_intro (l: list A): sublist nil l.
  Proof.   destruct l;simpl;auto. Qed.
  Lemma sublist_reflex (l: list A): sublist l l.
  Proof. induction l;simpl.
         auto. destruct (a==a) eqn:H; [auto | conflict_eq].  Qed.

 
  Lemma sublist_elim1 (l: list A): sublist l nil -> l=nil.
  Proof. destruct l; [auto | simpl; intro H; inversion H]. Qed.

  Lemma sublist_elim2 (a:A)(l s: list A): sublist (a::l) s -> In a s.
  Proof. induction s.  simpl; auto. simpl. destruct (a==a0) eqn:H. move /eqP in H.
         subst a0; auto. intro;right;auto. Qed.
  
  Lemma sublist_elim3 (a: A)(l s: list A): sublist (a::l) s -> sublist l s.
  Proof. { revert l; revert a. induction s.
         { auto. }
         { intros a0 l. 
           simpl. destruct (a0 == a) eqn:H.
           { destruct l. auto.  destruct (e == a) eqn:H1.
             apply IHs. auto.  }
           { destruct l. auto.  destruct (e == a) eqn:H1.
             { intro H2. assert (H2a: sublist (e::l) s). eapply IHs;exact H2.
               eapply IHs; exact H2a. }
             { apply IHs. }
         } } } Qed.
  
  Lemma sublist_elim3a (a e: A)(l s: list A): sublist (a::l)(e::s)-> sublist l s.
  Proof. simpl. destruct (a==e) eqn:H. auto.   eauto using sublist_elim3. Qed.
  
   Lemma sublist_intro1 (a:A)(l s: list A): sublist l s -> sublist l (a::s).
   Proof.  { revert s;revert a. induction l.
           { auto. }
           { intros a0 s.
             simpl. destruct (a == a0) eqn:H. apply sublist_elim3. auto. } } Qed.

   Lemma sublist_Subset (l s: list A): sublist l s -> Subset l s.
   Proof. { revert s. induction l.  eauto.
           intros s H. eauto. unfold "[<=]". intros x H1.
           destruct H1. subst x. eauto using  sublist_elim2. apply sublist_elim3 in H.
           apply IHl in H. eauto. } Qed.

  
   Lemma sublist_elim4 (l s: list A): sublist l s -> (forall a, count a l <= count a s).
   Proof. { revert l. induction s as [| e s'].
          { intro l. intro H. assert (H1: l=nil); auto using sublist_elim1.
            subst l; auto.  }
          { intros l H x. destruct l as [|a l'].
            simpl. lia. destruct (x==a) eqn:Hxa.
            { move /eqP in Hxa. subst x.
              simpl in H. destruct (a == e) eqn: Hae. move /eqP in Hae.
              subst e.
              cut (count a l' <= count a s'); auto.
              assert (H1: count a (a :: l') <= count a  s'). eauto.
              cut (count a s' <= count a (e::s')). lia. auto. }
            { assert (H1: count x (a::l')<= count x s').
              { simpl. rewrite Hxa. eauto using sublist_elim3a. }
              cut (count x s' <= count x (e::s')). lia. auto. } } } Qed.
   
   (*

  Hint Extern 0 (is_true ( sublist ?x ?z) ) =>
  match goal with
  | H: is_true (sublist x  ?y) |- _ => apply (@sublist_trans  x y z)
  | H: is_true (sublist ?y  z) |- _ => apply (@sublist_trans  x y z) 
  end.
*)
    
 
  Hint Resolve sublist_intro sublist_intro1 sublist_reflex sublist_Subset sublist_elim1: core.
  Hint Resolve sublist_elim2 sublist_elim3 sublist_elim4: core.


  (* -------------- list inclusion (subset in multiset) ----------------------------------*)

  Fixpoint included (l s: list A): bool := match l with
                                        |nil => true
                                        | a::l1 => match (memb a s) with
                                                  |true => included l1 (delete a s)
                                                  |false => false
                                                  end
                                        end.
  Lemma included_intro1 (l: list A): included nil l.
  Proof.  auto. Qed. 
  
   Lemma included_refl (l: list A): included l l.
  Proof. { induction l. auto. simpl. destruct (a==a) eqn:H0. auto. move /eqP in H0. auto. } Qed.
  
  Lemma included_intro2 (a:A)(l s: list A): In a s -> included l (delete a s)-> included (a::l) s.
  Proof. { induction s. 
          { simpl. auto. } 
          { simpl. intros H1 H2. destruct H1. destruct (a==a0) eqn: H3. auto.
            move /eqP in H3. auto. destruct (a==a0) eqn: H3. simpl. exact.
            simpl.  assert (H4: memb a s). eauto. case (memb a s) eqn:H5.
            exact. auto. } } Qed.
   
   

  Lemma included_intro (l s: list A): (forall a, count a l <= count a s)-> included l s.
  Proof. { revert s. induction l. intros;apply included_intro1;auto.
           { intros s H. simpl.  case (memb a s) eqn:Has;move /membP in Has.
             apply IHl. intro x. destruct (EM x a).
             2:{  replace (count x l) with (count x (a::l)).
             replace (count x (delete a s)) with (count x s).
             all: eauto. } subst x. 
             replace (count a l) with ((count a (a::l)) -1). 
             replace (count a (delete a s)) with ((count a s)-1).
             specialize (H a).  lia.
             replace (count a s) with (S (count a (delete a s))). lia.
             symmetry; eauto.
             replace (count a (a :: l)) with (S (count a l)). lia.
             symmetry; eauto.
             specialize (H a). rewrite countP4 in H.
             replace (count a s) with 0 in H. inversion H. symmetry; eauto. } } Qed. 


    Lemma included_intro3 (l s: list A): sublist l s -> included l s.
  Proof.  intro H. assert (H2: (forall a, count a l <= count a s)). eapply sublist_elim4. exact. eapply included_intro in H2. exact. Qed.
  
  Lemma included_elim1 (l: list A): included l nil -> l=nil.
  Proof. induction l. auto. intros. inversion H. Qed. 
  
  Lemma included_elim2 (a:A)(l s: list A): included (a::l) s -> In a s.
  
  Proof. { induction l. 
          {simpl. destruct (memb a s) eqn:H. auto. intro. inversion H0. }
          { simpl. destruct (memb a s) eqn:H. auto. intro. inversion H0. }}Qed.
  
  Lemma included_elim3 (a:A)(l s: list A): included (a::l) s -> included l (delete a s).
  Proof. { induction s.  
          { simpl. auto. }
          { simpl. destruct (a==a0) eqn:H0. simpl. auto. simpl. intros H. 
            destruct (memb a s) eqn:H1. auto. auto. } } Qed. 


  Lemma included_elim (l s: list A): included l s-> (forall a, count a l <= count a s).
  Proof. { revert s. induction l. simpl. intros;lia. 
           intros s H x. apply included_elim2 in H as H1. apply included_elim3 in H as H2.
           assert (H3: count a l <= count a (delete a s)).  eapply IHl with (s:= (delete a s)).
           auto.  destruct (EM x a).
           subst x. replace (count a (a::l)) with (S(count a l)).
           replace (count a s) with (S( count a (delete a s))).
           lia. symmetry; eauto.  eauto.  
           replace (count x (a::l)) with (count x l).
           replace (count x s) with  (count x (delete a s)).
           eauto. all: symmetry;eauto. } Qed. 
    
  Lemma included_elim4 (a:A)(l s: list A): included (a::l) s -> included l s.
  Proof. { intro H. assert (H1: (forall a0, count a0 (a::l) <= count a0 s)).
           eapply included_elim. exact. eapply included_intro. 
           assert (H2:forall a0 : A, (count a0 l)<=(count a0 (a :: l))). eauto.
           intros. specialize (H1 a0). specialize (H2 a0). lia. } Qed.
  

Lemma included_elim4b (a:A) (l s: list A) : included l s -> included (a::l) (a::s).
Proof. { intro H. apply included_intro. intro x. simpl.
         destruct (x==a) eqn: H1. cut ((count x l)<= (count x s)).
        lia. all:apply included_elim;exact. } Qed.

Lemma included_elim4a (a:A) (l: list A) : included (delete a l) l.
Proof. { induction l. simpl. auto. simpl. destruct (a == a0) eqn: H0. 
assert (H1: (forall a1, count a1 l <= count a1 (a0::l))). intros.
 eapply countP5. apply included_intro in H1. exact. 
  assert (H3:(included (delete a l) l)-> (included (a0 :: delete a l) (a0 :: l))). 
  eapply included_elim4b. eapply H3 in IHl. exact. } Qed.
  
  

   Lemma included_elim5 (l s: list A): included l s -> Subset l s.
  Proof. { unfold "[<=]". 
          induction l.
          { simpl. intros. destruct H0. }
          { intros.  destruct H0. eapply included_elim2 in H as H2.
           subst a0. exact. apply IHl. eapply included_elim4 in H as H3. 
           exact. exact. } } Qed.
           
    Lemma included_elim6 (l s: list A)(a b: A)(lr: A->A-> bool)(Hanti: antisymmetric lr): Sorted lr (a::l) -> Sorted lr (b::s) ->
     included (a::l) (b::s)-> a<>b -> included (a::l) s. 
    Proof. { intros H1 H2 H3 H4. 
           assert (H5: forall x, count x (a::l) <= count x (b::s)).
           { eapply included_elim;auto. }
           eapply included_intro.
           intros x. simpl.
           destruct (x == a) eqn: Hxa.
           { (*-----x=a----*)
            specialize (H5 a) as H6. simpl in H6. replace (a==b) with false in H6.
            replace (a==a) with true in H6. move /eqP in Hxa. subst x. exact.
            auto. auto. }
            { (*-----x<>a-----*)
              destruct (x==b) eqn:Hxb.
              {  (*----x=b---*) 
               move /eqP in Hxb. subst x. replace (count b l) with 0. lia.
               symmetry. cut (~In b l). eauto. intro H6. 
               assert (H7: lr a b). eauto.
               assert (H8: lr b a). 
               { (*---lr b a ---*)
                cut (In a (b::s)). eauto. eapply included_elim2. exact H3.
                }
               absurd (a=b). auto. apply Hanti. split_;auto. }
              { (*--- x<>b----*) 
                 specialize (H5 x) as Hx.
                 simpl in Hx. rewrite Hxa in Hx. rewrite Hxb in Hx. exact. } } } Qed.
              
                 
                   
   
   
  Lemma included_trans (l1 l2 l3: list A): 
  included l1 l2-> included l2 l3 -> included l1 l3.
  Proof. { intros H1 H2. 
          assert (H1a:forall a0 : A, (count a0 l1)<=(count a0 l2)).
          eapply included_elim. exact.
          assert (H2a:forall a0 : A, (count a0 l2)<=(count a0 l3)).
          eapply included_elim. exact.
          eapply included_intro. intros a.
          specialize (H1a a). specialize (H2a a). lia. } Qed.

   Hint Extern 0 (is_true ( included ?x ?z) ) =>
  match goal with
  | H: is_true (included x  ?y) |- _ => apply (@included_trans  x y z)
  | H: is_true (included ?y  z) |- _ => apply (@included_trans  x y z) 
  end : core.

 
  Hint Resolve included_intro1 included_intro2 included_intro3: core.
  Hint Resolve included_refl included_intro: core.
  Hint Resolve included_elim1 included_elim2 included_elim3: core.
  Hint Resolve included_elim4 (* included_elim4a *) included_elim5 included_elim: core.

  (* ----- Some Misc Lemmas on nodup, sorted, sublist, subset and included ---------------- *)

  Lemma nodup_subset_included (l s: list A): NoDup l -> l [<=] s -> included l s.
  Proof. { intros H1 H2. eapply included_intro. intro a. assert (H: In a l -> In a s). eauto. assert (H3: forall x, In x l -> count x l <=1). eauto.
  specialize (H3 a) as H4. assert (H5:In a s -> count a s >=1). eauto.
  assert (H6:(In a l)\/( ~In a l)). eauto. destruct H6. apply H in H0 as H7.
  apply H5 in H7. apply H4 in H0. lia. assert (H6: count a l =0).
  eauto. replace (count a l) with 0. lia. } Qed.
 
  Lemma sublist_is_sorted (lr: A-> A-> bool)(l s: list A):  Sorted lr s -> sublist l s -> Sorted lr l. 
  Proof. { revert l.
           induction s as [|b s1].
           { intros l H1 H2. assert (H3:l=nil).
             eauto.  subst l. auto. }
           { intros l H1 H2.  
             destruct l as [|a l1].
             {  eapply Sorted_elim3. apply Sorted_single. Unshelve. exact. }
             { simpl in H2.
               destruct (a == b) eqn: Hab.
               { (*----a=b----*)
                 move /eqP in Hab. constructor. 
                 { apply IHs1. eauto. exact. }
                 { intros x H3. 
                   assert (H4: lr b x). 
                   { cut (In x s1). apply Sorted_elim4. exact.
                   assert (H5: l1 [<=] s1). auto. auto. }
                 subst a;auto. } }
               { (*---a<>b---*)
                 apply IHs1.  eauto. exact.  } } } } Qed.     
             
  
  
  Lemma sorted_included_sublist (l s: list A)(lr: A->A-> bool)(Hanti: antisymmetric lr):
    Sorted lr l-> Sorted lr s-> included l s-> sublist l s.
  Proof. { revert l.
           induction s as [|b s1]. 
           { intros l H1 H2 H3. destruct l;simpl in H3. simpl;auto.
            inversion H3. }
           { intros l H1 H2 H3. 
             destruct l as [|a l1] eqn: H4. 
             { simpl;auto. }
             { (*----sublist (a :: l1) (b :: s1)-----*)
               simpl. destruct (a==b) eqn: Hab. 
               { (*----- a = b --------*)
               apply IHs1. eauto. eauto. move /eqP in Hab. subst b.
               cut (forall x, count x l1 <= count x s1). eauto.
               intros x. 
               assert (H5: forall y, count y (a :: l1) <= count y (a :: s1)).            
               eapply included_elim. exact. specialize (H5 x) as H6. simpl in H6. 
               destruct (x == a);lia. }
               { (*------ a <> b--------*) 
                assert (H5: included (a::l1) s1). eapply included_elim6. 
                exact Hanti. auto. exact H2. exact H3. move /eqP in Hab.  exact.
                eapply IHs1. exact. eauto. exact. } } } } Qed.
  
  Lemma first_in_ordered_sublists (a e:A)(l s: list A)(lr: A->A-> bool)(Hrefl: reflexive lr):
    Sorted lr (a::l)-> Sorted lr (e::s)-> sublist (a::l)(e::s)-> lr e a.
  Proof. { intros H1 H2 H3. simpl in H3. destruct (a == e) eqn: H4.
         move /eqP in H4. subst a. auto.
         assert (H5: (forall x, In x l -> lr a x)). eapply Sorted_elim4. exact.
         assert (H6: (forall x, In x s -> lr e x)). eapply Sorted_elim4. exact.
         eauto. } Qed.

 Lemma nodup_included_nodup (l s: list A) :
 NoDup s -> included l s -> NoDup l.
 Proof. { intros. assert (H1:(forall a, count a l <= count a s)).
        apply included_elim. exact. apply count_nodup. intros.
        specialize (H1 x) as H3. assert (H4: count x s <=1).
        apply nodup_count. exact. eauto. lia. } Qed.
 
 Lemma subset_nodup_subset (a:A) (l s: list A) :
 l[<=]a::s-> NoDup l -> ~In a l -> l[<=]s.
 Proof. { intros. unfold Subset in H. unfold Subset. intros.
       specialize (H a0) as H3. apply H3 in H2 as H4. simpl in H4.
       destruct H4. subst a. absurd (In a0 l). exact. exact. exact. } Qed.
  

       
  Hint Resolve nodup_subset_included: core.
  Hint Immediate sorted_included_sublist first_in_ordered_sublists
  nodup_included_nodup :core.
  

  (* --------------------  permuted lists (permutation) -------------------------------------*)

  Definition perm (l s: list A): bool:= included l s && included s l. 

  Lemma perm_intro  (l s: list A): (forall a, count a l = count a s)-> perm l s.
  Proof.  { intro H; split_; apply included_intro; intro a; specialize (H a); lia. } Qed.

  Lemma perm_intro0a (l: list A)(lr: A-> A-> bool): perm l (sort lr l).
  Proof. apply perm_intro. eauto. Qed.
  
  Lemma perm_intro0b (l: list A)(lr: A-> A-> bool): perm (sort lr l) l.
  Proof. apply perm_intro; eauto. Qed.
 
  Lemma perm_nil: perm nil nil.
  Proof. split_; eauto.  Qed.
  
  Lemma perm_refl (l: list A): perm l l.
  Proof. split_; eauto.  Qed.

  Lemma perm_intro3 (l s: list A): sublist l s -> sublist s l -> perm l s.
  Proof. intros; split_; eauto.  Qed.

  Lemma perm_elim   (l s: list A): perm l s -> (forall a, count a l = count a s).
  Proof.  { intros H a. move /andP in H. destruct H as [H1 H2].
          cut (count a l <= count a s). cut (count a s <= count a l). lia.
          all: eauto. } Qed.

  Lemma perm_elim1 (l: list A): perm l nil -> l = nil.
  Proof. intro H; move /andP in H; destruct H as [H1 H2]; eauto. Qed.
  Lemma perm_elim2 (l s: list A): perm l s -> l [=] s.
  Proof. move /andP;intro H; destruct H; split; eauto. Qed.
  Lemma perm_sym (l s: list A): perm l s -> perm s l.
  Proof. move /andP;intro H; apply /andP; tauto. Qed.

  Lemma perm_trans (x y z: list A): perm x y -> perm y z -> perm x z.
  Proof. intros H H1; move /andP in H; move /andP in H1; apply /andP.
         split;destruct H; destruct H1. all: auto. Qed.

  Hint Extern 0 (is_true ( perm ?x ?z) ) =>
  match goal with
  | H: is_true (perm x  ?y) |- _ => apply (@perm_trans x y z)
  | H: is_true (perm ?y  z) |- _ => apply (@perm_trans x y z) 
  end : core.

  Hint Resolve  perm_intro0a  perm_intro0b perm_refl perm_nil perm_elim1 : core.
  Hint Immediate perm_elim perm_intro perm_sym: core.
  
  Lemma perm_sort1 (l s: list A)(lr: A-> A-> bool): perm l s -> perm  l (sort lr s).
  Proof.  eauto. Qed.

   Lemma perm_sort2 (l s: list A)(lr: A-> A-> bool): perm l s -> perm  (sort lr l) s.
   Proof. eauto.  Qed.

   Lemma perm_sort3 (l s: list A)(lr: A-> A-> bool): perm l s -> perm (sort lr l)(sort lr s).
   Proof. eauto using perm_sort1. Qed.
   
   Lemma countP1a (l:list A) (x:A): count x l >=1 -> In x l.
   Proof. { induction l. simpl. intros H. lia. simpl.  intros H. 
          destruct (x == a) eqn: H1. left. move /eqP in H1. symmetry;exact.
          right. eapply IHl in H. exact. } Qed.
   
   Lemma perm_nodup (l s: list A): perm l s -> NoDup l -> NoDup s.
   Proof. { intros. apply count_nodup. intros.
          assert (H2: forall x, In x l -> count x l <= 1). 
          eauto. assert (H3: forall a, count a l = count a s).
          eauto. specialize (H2 x) as H4. specialize (H3 x) as H5.
          assert (H6: count x s >=1). eauto.
          assert (H7: count x l>=1). lia.  
          assert (H8:In x l). apply countP1a. exact. apply H4 in H8. lia. } Qed.

   Lemma perm_subset (l1 l2 s1 s2: list A): perm l1 l2 -> perm s1 s2 -> l1 [<=] s1 -> l2 [<=] s2.
   Proof. intros. unfold perm in H. unfold perm in H0. move /andP in H.
   move /andP in H0. destruct H. destruct H0. eapply included_elim5 in H2.
   eapply included_elim5 in H0. eauto. Qed.
   

   Lemma perm_elim3 (l s: list A)(a: A): perm l s -> perm (a::l) (a::s).
   Proof.  unfold perm. intros. move /andP in H. destruct H. apply /andP.
   split. eapply included_elim4b. exact. eapply included_elim4b. exact. Qed.
   
   
   

   Hint Resolve perm_sort1 perm_sort2 perm_sort3 perm_nodup perm_subset: core.
   
 End Permutation. 




  Hint Resolve count_in_putin1 count_in_putin2 count_in_sorted: core.


  Hint Resolve sublist_intro sublist_intro1 sublist_reflex sublist_Subset sublist_elim1: core.
  Hint Resolve sublist_elim2 sublist_elim3 sublist_elim3a sublist_elim4: core.
(*
  Hint Extern 0 (is_true ( sublist ?x ?z) ) =>
  match goal with
  | H: is_true (sublist x  ?y) |- _ => apply (@sublist_trans _ x y z)
  | H: is_true (sublist ?y  z) |- _ => apply (@sublist_trans _ x y z) 
  end.

*)
  Hint Resolve included_intro1 included_intro2 included_intro3: core.
  Hint Resolve included_refl included_intro: core.
  Hint Resolve included_elim1 included_elim2  included_elim3: core.
  Hint Resolve included_elim4 (*included_elim4a*) included_elim5 included_elim: core.
  
  Hint Extern 0 (is_true ( included ?x ?z) ) =>
  match goal with
  | H: is_true (included x  ?y) |- _ => apply (@included_trans _ x y z)
  | H: is_true (included ?y  z) |- _ => apply (@included_trans _ x y z) 
  end : core.

  Hint Resolve nodup_subset_included: core.
  Hint Immediate sorted_included_sublist first_in_ordered_sublists
  nodup_included_nodup :core.
  Hint Resolve  perm_intro0a  perm_intro0b perm_refl perm_nil perm_elim1 : core.
  Hint Immediate perm_elim perm_intro perm_sym: core.
  Hint Resolve perm_elim1 perm_elim2 perm_elim3: core.

  Hint Extern 0 (is_true ( perm ?x ?z) ) =>
  match goal with
  | H: is_true (perm x  ?y) |- _ => apply (@perm_trans _ x y z)
  | H: is_true (perm ?y  z) |- _ => apply (@perm_trans _ x y z) 
  end : core.

  Hint Resolve perm_sort1 perm_sort2 perm_sort3 perm_nodup perm_subset: core.
