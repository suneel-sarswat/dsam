
(*Commnet Here*)

Require Import ssreflect ssrbool. 
Require Export Lists.List.
Require Export GenReflect SetSpecs.
Require Import Lia.
Require Import Wf.
From Equations Require Import Equations.

Require Export DecSort MinMax.
Require Export mBidAsk.
Require Export DecList.
Require Export mMatching.
Require Export Quantity.
Require Export mFair_Bid.


Section Fair_Ask.

Definition fair_on_asks (M: list fill_type) (A: list Ask):=
  (forall s s', In s A /\ In s' A -> s < s' -> In s' (asks_of M) ->
  (ttqa M s')>0 -> 
  (In s (asks_of M)/\(ttqa M s= sq s))).

(*##################Sorting Criteria for Bids and Matchings for fair #################*)

Definition by_sp (s1:Ask) (s2:Ask) :=(Nat.leb s1 s2) ||
((Nat.eqb s1 s2) && (Nat.leb (stime s1)  (stime s2) )).
Lemma comp_triv (sp:nat)(sp0:nat):
~ (Nat.leb sp sp0) -> (Nat.leb sp0 sp).
Proof. revert sp. induction sp0. simpl. intro. eauto. intros. 
 simpl in H. destruct sp. simpl. auto. intros. simpl. eapply IHsp0. auto. Qed.
Lemma by_sp_P : transitive by_sp /\ comparable by_sp.
Proof. { split.
          { unfold transitive. unfold by_sp.  
            intros y x z H H1. move /orP in H1. move /orP in H.
            apply /orP. destruct H1;destruct H. 
            { left. move /leP in H0. move /leP in H. apply /leP. lia. }
            { move /andP in H. destruct H. left.  
              move /leP in H0. move /eqP in H. apply /leP. lia. }
            { move /andP in H0. destruct H0. left.
              move /leP in H. move /eqP in H0. apply /leP. lia. }
            { move /andP in H0. move /andP in H. destruct H0. destruct H.
              left.
              move /eqP in H. move /eqP in H0. apply /leP. lia. } }
          { unfold comparable. unfold by_sp. intros. move /orP in H.
            assert (~ ((Nat.leb x y))). eauto. apply /orP. left.
            destruct x. destruct y. simpl in H0. simpl in H. simpl.
            apply comp_triv. auto. } } Qed.

                
Lemma by_sp_refl: reflexive by_sp.
Proof. unfold reflexive. intros. unfold by_sp. apply /orP. 
left. apply nat_reflexive.  Qed.


Definition m_sp (m1:fill_type) (m2:fill_type) := by_sp (ask_of m1) (ask_of m2).

Lemma m_sp_P : transitive m_sp /\ comparable m_sp.
Proof. { split.
         { unfold transitive. unfold m_sp. 
           intros. cut (transitive by_sp). intros. eauto using by_sp_P. 
            apply by_sp_P. }
         { unfold comparable.  unfold m_sp. intros x y H. eapply by_sp_P. 
           exact.  } } Qed. 

Lemma m_sp_refl: reflexive m_sp.
Proof. unfold reflexive. intros. unfold m_sp. unfold by_sp. 
apply /orP. left. apply nat_reflexive. Qed.

Lemma m_sp_and_by_sp (M:list fill_type):
Sorted m_sp M -> Sorted by_sp (asks_of M).
Proof. intros. induction M. simpl. constructor. simpl. inversion H.
assert(exists a0, a0=(ask_of a)). eauto.
destruct H4. rewrite <- H4.
constructor. apply IHM. eauto. intros.
assert (exists m0, (In m0 M)/\(x0=(ask_of m0))).
eapply asks_of_elim. auto.
destruct H6. destruct H6. apply H3 in H6. unfold m_sp in H6.
subst. auto. Qed.

Hint Resolve m_sp_P by_sp_P : core.
Hint Resolve by_sp_refl m_sp_refl : core.



(*####################################################################################*)
  
(*----------------  Function to make a matching fair on bids -----------------------*)

(*####################################################################################*)


Equations FOA_aux (M:list fill_type) (A: list Ask) (t: nat): 
(list fill_type) by wf (|M| + |A|):=
FOA_aux nil _ _ := nil;
FOA_aux _ nil _:= nil;
FOA_aux (m::M') (a::A') t:=  if (Nat.eqb (tq m) (sq a - t)) then 

(Mk_fill (bid_of m) a (sq a - t) (tp m))::(FOA_aux M' A' 0) 

else (if (Nat.leb (tq m) (sq a - t)) then

(Mk_fill (bid_of m) a (tq m) (tp m)):: (FOA_aux M' (a::A') (t + tq m))

else 

(Mk_fill (bid_of m) a (sq a - t) (tp m)):: 
(FOA_aux ((Mk_fill (bid_of m) (ask_of m) (tq m - (sq a - t)) (tp m))::M') A' 0)).

Next Obligation.
lia. Qed.
Next Obligation.
lia. Qed.

Definition FOA (M:list fill_type) (A: list Ask) := FOA_aux M A 0.


(*################################################################################*)
(*Lemma on subsets: The list of Bids of FOA is subset of B 
  and the Asks are subset of input M*)
(*################################################################################*)


(*################################################################################*)
(*Lemma on subsets: The list of Bids of FOA is subset of B 
  and the Asks are subset of input M*)
(*################################################################################*)

Lemma FOA_aux_asks_subset (M: list fill_type) (A:list Ask)(t:nat) :
asks_of (FOA_aux M A t) [<=] A.
Proof. apply FOA_aux_elim. all: auto.
{
 intros. destruct (Nat.eqb (tq f) (sq a - t0)) eqn: Hfb. 
 { simpl. cut (asks_of (FOA_aux l l0 0) [<=] l0). auto. exact H. }
 { destruct (Nat.leb (tq f) (sq a - t0)) eqn: Hbf. 
 { simpl. eapply subset_elim1. apply H0. }
 {  simpl. eapply subset_elim2. exact H1. }
 } 
}
Qed.
           
Lemma FOA_aux_bids_subset (M: list fill_type) (A: list Ask) (t:nat):
bids_of (FOA_aux M A t) [<=] bids_of M.
Proof. apply FOA_aux_elim. all: auto.
{
 intros. destruct (Nat.eqb (tq f) (sq a - t0)) eqn: Hfb. 
 { simpl. cut (bids_of (FOA_aux l l0 0) [<=] bids_of l). 
   auto. move /eqP in Hfb. 
   assert ((tq f - (sq a - t0)) =0). lia.  exact H. 
 }
 { destruct (Nat.leb (tq f) (sq a - t0)) eqn: Hbf. 
   { simpl. eapply subset_elim2. apply H0. }
   { simpl. simpl in H1. eapply subset_elim1. exact H1. }
 }
}
Qed.

Lemma FOA_aux_tp_subset (M: list fill_type) (A: list Ask) (t:nat):
trade_prices_of (FOA_aux M A t) [<=] trade_prices_of M.
Proof. apply FOA_aux_elim. all: auto.
{
 intros. destruct (Nat.eqb (tq f) (sq a - t0)) eqn: Hfb. 
 { simpl. cut (trade_prices_of (FOA_aux l l0 0) [<=] trade_prices_of l). 
   auto. move /eqP in Hfb. 
   assert ((tq f - (sq a - t0)) =0). lia.  exact H. 
 }
 { destruct (Nat.leb (tq f) (sq a - t0)) eqn: Hbf. 
   { simpl. eapply subset_elim2. apply H0. }
   { simpl. simpl in H1. eapply subset_elim1. exact H1. }
 }
}
Qed.


Lemma FOA_subA (M: list fill_type)(A: list Ask): bids_of (FOA M A) [<=] bids_of M.
Proof. { unfold FOA. apply FOA_aux_bids_subset. } Qed.
Lemma FOA_subB (M:list fill_type) (A: list Ask): asks_of (FOA M A) [<=] A.
Proof. { unfold FOA. apply FOA_aux_asks_subset. } Qed. 



(*################################################################################*)
(*Lemmas: Total traded quantity *)

(*################################################################################*)



(*This lemma (fob_asks_invariant) ensures that the total traded quantity for each ask in FOA is equal to it's  traded quantity in the input atching M. With this it is starightforward that the total traded quantity of an ask in FOA is less than or equal to it's  ask quantity, since M is a matching. This lemma is also useful to ensures that the asks are not changed during fair on bids. This is useful to prove that during composition of FOA to FOA functions the fairness property of FOA remains invariant. This lemaa is also useful to show that the total traded quantity of FOA is same as input M. *)

Lemma FOA_aux_bids_invariant_t (M:list fill_type)(A: list Ask)(b:Bid)(t:nat)
(NZT:(forall m, In m M -> (tq m) > 0) ):
QA(A)>=QM(M)+t -> ttqb M b = ttqb (FOA_aux M A t) b.
Proof.
funelim (FOA_aux M A t). all:auto.
+ intros. simpl in H. assert(tq f =0). lia. assert(tq f >0). apply NZT. auto.
rewrite H0 in H1. inversion H1.
+ intros. rewrite <- Heqcall. destruct (Nat.eqb (tq f) (sq a - t)) eqn:Heq0. 
{ simpl. destruct (b_eqb b (bid_of f)) eqn:Ham. 
 cut (ttqb l b = ttqb (FOA_aux l l0 0) b). auto. 
 all: eapply H. all: try (simpl; lia);auto;eauto.
 all: simpl in H2. all:move /eqP in Heq0. lia. lia. }
{ intros. destruct (Nat.leb (tq f) (sq a - t)) eqn: Hle. 
{ simpl. simpl in H2. 
move /leP in Hle. move /eqP in Heq0. destruct (b_eqb b (bid_of f)) eqn:Ham. 
cut( ttqb l b = ttqb (FOA_aux l (a :: l0) (t + tq f)) b). auto.
 eapply H0. all: try (simpl; lia);auto.
eapply H0. all: try (simpl; lia);auto. }
{ simpl. simpl in H2. 
move /leP in Hle. move /eqP in Heq0. 
assert (ttqb (FOA_aux 
      ({|bid_of := bid_of f;
      ask_of := ask_of f;
       tq := tq f - (sq a - t);
      tp := tp f |} :: l) 
      l0 0) b = 
      ttqb ({|bid_of := bid_of f;
      ask_of := ask_of f;
       tq := tq f - (sq a - t);
      tp := tp f |} :: l) b). symmetry. 
      (*Handle this situation in general, try to clean it using ltac*)
 eapply H1. all: try (simpl; lia);auto. 
 { intros. simpl in H3. destruct H3. subst m. simpl. lia. auto. } rewrite H3.
 simpl. destruct (b_eqb b (bid_of f)) eqn:Ham. simpl. lia. lia. } } Qed.


Lemma FOA_bids_invariant (M:list fill_type)(A: list Ask)(b:Bid)
(NZT:(forall m, In m M -> (tq m) > 0) ):
QA(A)>=QM(M) -> ttqb M b = ttqb (FOA M A) b.
Proof. unfold FOA. intros. eapply FOA_aux_bids_invariant_t. auto. lia. Qed.

(*################################################################################*)

(*Lemmas: Fair property *)

(*################################################################################*)

(*In this lemma (fob_aux_top_bid_fair) we first show that the top bid in B is fully traded (trade quantity is total quantity. Note that, for arbitrary value of t, the statement is total quantity minus t. For t=0, the statement of following lemma is same as fully traded*)

Lemma FOA_aux_top_ask_fair (M: list fill_type)(A: list Ask)(a:Ask)(t:nat)
(NZT:(forall m, In m M -> (tq m) > 0) )(NDA:NoDup (a::A)):
QM(M)>=(sq a) - t -> ttqa (FOA_aux M (a::A) t) a = sq a - t.
Proof. 
revert t A a NDA. induction M as [ | m M']. intros.
simp FOA_aux. simpl. simpl in H. lia.
{ intros. simp FOA_aux. destruct (Nat.eqb (tq m) (sq a -t )) eqn: Heq0. 
{ 
simpl.  assert(a_eqb a a = true). eauto. rewrite H0.
cut (ttqa (FOA_aux M' A 0) a = 0). lia.
assert (~In a A). eauto.
 assert (forall t, asks_of (FOA_aux M' A t) [<=] A). intros.
  eapply FOA_aux_asks_subset with (M:=M')(t:=t0)(A:=A).
 assert (forall t, ~In a (asks_of (FOA_aux M' A t))).  intros. specialize (H2 t0).
 eauto. apply ttqa_elim. auto. }
{ intros. destruct (Nat.leb (tq m) (sq a - t)) eqn: Hle. 
{ simpl. assert(a_eqb a a = true). eauto. rewrite H0. 
assert (ttqa (FOA_aux M' (a :: A) (t+tq m)) a = sq a - (t+tq m)).
apply IHM'. auto. exact NDA. simpl in H. move /leP in Hle. lia. 
move /leP in Hle. rewrite H1. lia. }
{ simpl. 
assert(a_eqb a a = true). eauto. rewrite H0. 
cut (ttqa (FOA_aux ({|bid_of := bid_of m;
      ask_of := ask_of m;
      tq := tq m - (sq a - t);
      tp := tp m |} :: M') A 0) a = 0). lia.
assert (~In a A). eauto.
 assert (asks_of (FOA_aux ({|bid_of := bid_of m;
      ask_of := ask_of m;
      tq := tq m - (sq a - t);
      tp := tp m |} :: M') A 0) [<=] A). eapply FOA_aux_asks_subset.
 assert (~In a (asks_of (FOA_aux ({|bid_of := bid_of m;
      ask_of := ask_of m;
      tq := tq m - (sq a - t);
      tp := tp m |} :: M') A 0))).  
 eauto. apply ttqa_elim. auto. }} } Qed.


(*Special case of above lemma for t=0 *)
Lemma FOA_aux_top_ask_fair0 (M: list fill_type)(A: list Ask)(a:Ask)
(NZT:(forall m, In m M -> (tq m) > 0) )(NDA:NoDup (a::A)):
QM(M)>=(sq a)-> ttqa (FOA M (a::A)) a = sq a.
Proof.
unfold FOA.
cut(QM(M)>=(sq a) - 0-> ttqa (FOA_aux M (a::A) 0) a = sq a - 0). lia.
eapply FOA_aux_top_ask_fair with (t:=0)(a:=a)(M:=M). exact. exact. Qed.

(*This lemma ensures that if a less move competitive ask is part of FOA then less competitive 
must be part of matching.*)
Lemma FOA_aux_more_competative_in (M: list fill_type)(A: list Ask)(a1 a2:Ask)(t:nat)
(NZT:(forall m, In m M -> (tq m) > 0) )(NDA:NoDup A):
Sorted by_sp A ->
a1<a2 -> 
In a1 A ->
In a2 A ->
In a2 (asks_of (FOA_aux M A t))-> 
In a1 (asks_of (FOA_aux M A t)).
Proof. 
funelim (FOA_aux M A t). 
+ intros. simp FOA_aux in H1. 
+ intros. simp FOA_aux in H1.
+ intros. destruct (a_eqb a a1) eqn: Hbb1;destruct (a_eqb a a2) eqn: Hbb2.
{ move /eqP in Hbb1;move /eqP in Hbb2.
  subst a1;subst a2. lia. }
{ move /eqP in Hbb1;subst a1. 
  rewrite <- Heqcall.
  destruct (Nat.eqb (tq f) (sq a - t)) eqn:Heq0.  
  simpl. left;auto.
  destruct (Nat.leb (tq f) (sq a - t)) eqn:Hle.
  simpl. left;auto.
  simpl. left;auto.
}
{ move /eqP in Hbb2;subst a2.
  { eapply Sorted_elim4 with (a0:=a)(x:=a1) in H2. 
    unfold by_sp in H2.
    move /orP in H2. destruct H2. 
    move /leP in H2. lia. move /andP in H2;destruct H2.
    move /eqP in H2. lia. auto. destruct H4.
    subst a1. lia. exact.      
  }
}
{
  destruct H4;destruct H5.
  { subst a. move /eqP in Hbb1. elim Hbb1;auto. } 
  { subst a. move /eqP in Hbb1. elim Hbb1;auto. }
  { subst a. move /eqP in Hbb2. elim Hbb2;auto. }
  { rewrite <- Heqcall. rewrite <- Heqcall in H6.
    destruct (Nat.eqb (tq f) (sq a - t)) eqn: Heq.
    { simpl. simpl in H6. destruct H6.
      { subst a. move /eqP in Hbb2. elim Hbb2;auto. }
      { right. eapply H. auto. all:eauto. }
    }    
    { destruct (Nat.leb (tq f) (sq a - t)) eqn: Hle.
      { simpl. simpl in H6. destruct H6.
        { subst a. move /eqP in Hbb2. elim Hbb2;auto. }
        { right. eapply H0. auto. all:eauto. }
      }
      { simpl. simpl in H6. destruct H6.
        { subst a. move /eqP in Hbb2. elim Hbb2;auto. }
        { right. eapply H1. auto. 
          intros. simpl in H7. destruct H7. subst m.
          simpl. move /eqP in Heq. move /leP in Hle. lia. 
           all:eauto. 
        }
      }
    }
  }    
} Qed.  
    

(*Following lemma (TQ_FM) ensures that if a less competitive bid is part of FOA_aux then 
the total quantity traded in the matching should be more that or equal to more competitive bid*)

Lemma FOA_QM_ge_bqb (M: list fill_type)(A: list Ask)(a1 a2:Ask)(t:nat)
(NZT:(forall m, In m M -> (tq m) > 0) )(NDA:NoDup A):
Sorted by_sp A ->  a1<a2 -> 
In a1 (asks_of (FOA_aux M A t)) -> In a2 (asks_of (FOA_aux M A t))
->  QM(M)>=sq a1 - t.
Proof.  funelim (FOA_aux M A t). 
+ intros. simp FOA_aux in H1. simpl in H1;elim H1.
+ intros. simp FOA_aux in H1. simpl in H1;elim H1.
+ intros. rewrite <- Heqcall in H4. rewrite <- Heqcall in H5.
destruct (Nat.eqb (tq f) (sq a - t)) eqn:Heq0.  
{  (*Case : EQ *)
   simpl in H4. simpl in H5. move /eqP in Heq0. destruct H4;destruct H5. 
   { subst a1. simpl. lia. }
   { subst a1. simpl. lia. }
   { (*this case contradict sorted. Move this into 
     a general result and automate. *)subst a2. assert (In a1 l0). eapply FOA_aux_asks_subset.
     eauto. assert(a<a1). 
     { eapply Sorted_elim4 with (a0:=a)(x:=a1) in H2. unfold by_sp in H2.
     move /orP in H2. destruct H2. move /leP in H2. lia. move /andP in H2;destruct H2.
     move /eqP in H2. lia. auto. }
    lia. } 
   { eapply H in H3. all: try (simpl;lia);auto;eauto. } 
}   (*End Case : EQ*)
{ 
   destruct (Nat.leb (tq f) (sq a - t)) eqn: Hle. 
   { (*Case : Top trade quantity is less than the the top bid  *)
     move /eqP in Heq0. move /leP in Hle. simpl in H4. simpl in H5.
     destruct H4;destruct H5. 
      { subst. inversion H3. lia. lia. }
      { subst a. eapply H0 in H3. all: try (simpl;lia);auto. 
       { case l eqn:Hl.  simp FOA_aux in H5. simp FOA_aux.
         destruct (Nat.eqb (tq f0) (sq a1 - (t + tq f))) eqn:Hfb1. 
         simpl. left. auto. 
         destruct (Nat.leb (tq f0) (sq a1 - (t + tq f))) eqn: Hfble.
         simpl;left;auto. 
         simpl;left;auto.   } 
      }
      { subst a2. assert (In a1 (a::l0)). 
        eapply FOA_aux_asks_subset with (A:=(a::l0)).
        eauto. assert(a<a1). 
        { eapply Sorted_elim4 with (a0:=a)(x:=a1) in H2. 
          unfold by_sp in H2.
          move /orP in H2. destruct H2. 
          move /leP in H2. lia. move /andP in H2;destruct H2.
          move /eqP in H2. lia. destruct H5. subst a. lia. auto. 
        } lia. 
      }
      { eapply H0 with (a1:=a1) in H5. all: try (simpl;lia);auto. } 
   }
   { (*Case : Top trade quantity is more than the the top bid  *)
     move /eqP in Heq0. move /leP in Hle. simpl in H4. simpl in H5.
     destruct H4;destruct H5.
     { subst. inversion H3. lia. lia. }
     { subst a. simpl. lia. }
     { eapply Sorted_elim4 with (a0:=a)(x:=a1) in H2. 
       unfold by_sp in H2.
       move /orP in H2. destruct H2. move /leP in H2. subst a. simpl. lia. 
       move /andP in H2;destruct H2. move /eqP in H2. simpl. subst a. lia. 
       eapply FOA_aux_asks_subset with (A:=(l0)) in H4. exact. 
     }
     { eapply H1 with (a1:=a1) in H5. simpl in H5. all: try (simpl;lia);auto. 
      intros. simpl in H6. destruct H6. subst m. all: try (simpl;lia);auto;eauto. 
     } 
   } 
}   Qed.
      
Lemma FOA_aux_triv (l:list fill_type):
FOA_aux l nil 0 =nil.
Proof. funelim (FOA_aux l nil 0). simp FOA_aux. auto. simp FOA_aux. auto. Qed.

(*Following lemma (fob_aux_bids_fair_t) is the main fair lemma for arbitrary value of t.
  Note that, for t=0 the lemma is fair_on_bids lemma.*)
Lemma FOA_aux_asks_fair_t (M: list fill_type)(A: list Ask)(a a1 a2:Ask)(t:nat)
(NZT:(forall m, In m M -> (tq m) > 0) )(NDA:NoDup (a::A)):
Sorted by_sp (a::A) ->  
a1<a2 -> 
In a1 (asks_of (FOA_aux M (a::A) t)) -> 
In a2 (asks_of (FOA_aux M (a::A) t)) ->  
(a1=a -> ttqa (FOA_aux M (a::A) t) a1 = sq a1 - t )/\
(a1<>a->ttqa (FOA_aux M (a::A) t) a1 = sq a1 ).
Proof.
funelim (FOA_aux M (a::A) t). auto. 
{ intros. destruct (a_eqb a1 a ) eqn: Hbb1. 
  { move /eqP in Hbb1. subst a. split.
    intros. eapply FOA_aux_top_ask_fair. auto. auto. eapply FOA_QM_ge_bqb in H5. 
    all: try (simpl;lia);auto;eauto.  
  }
  { split;intros. 
    { subst a1. move /eqP in Hbb1. auto. }
    { rewrite<- Heqcall. 
      destruct (Nat.eqb (tq f) (sq a - t)) eqn:Hmb. (*EQ case when a1<>a *)
      { simpl. rewrite Hbb1. 
        rewrite<- Heqcall in H4. simpl in H4. 
        rewrite<- Heqcall in H5. simpl in H5. 
        destruct H4;destruct H5. 
        { subst a1;auto. }
        { subst a1;auto. }
        { subst a2. assert (In a1 l0). 
          eapply FOA_aux_asks_subset. eauto.
          assert(a<a1). 
          { eapply Sorted_elim4 with (a0:=a)(x:=a1)(lr:=by_sp) in H2. 
            unfold by_sp in H2. move /orP in H2. destruct H2. 
            move /leP in H2. lia. move /andP in H2;destruct H2.
            move /eqP in H2. lia. auto.  } 
            lia. }
         { case l0 as [| b0 A'] eqn:Hl0.
             { rewrite FOA_aux_triv in H4. simpl in H4. auto. }
             { destruct (a_eqb a1 b0) eqn: Hbb0. 
                  { move /eqP in Hbb0. subst b0. eapply FOA_aux_top_ask_fair0.
                    auto. eauto. eapply FOA_QM_ge_bqb with (a1:=a1)(A:=(a1::A'))(a2:=a2) in H5.
                    lia. auto. eauto. eauto. all:exact. }
                  { eapply H. auto. eauto. auto. auto. eauto. eauto. 
                    exact. exact. move /eqP in Hbb0. exact. } 
             } 
         } 
      }
      { destruct (Nat.leb (tq f) (sq a - t)) eqn: Hle.
           (*Less than case *) 
        { rewrite <- Heqcall in H4. simpl in H4.
          rewrite <- Heqcall in H5. simpl in H5.
          move /eqP in Hmb. move /leP in Hle.
          destruct H4;destruct H5. 
          { subst a1;auto. }
          { subst a1;auto. }
          { subst a2. assert (In a1 (a::l0)). 
            eapply FOA_aux_asks_subset. eauto.
            assert(a<a1). 
            { eapply Sorted_elim4 with (a0:=a)(x:=a1)(lr:=by_sp) in H2. 
            unfold by_sp in H2. move /orP in H2. destruct H2. 
            move /leP in H2. lia. move /andP in H2;destruct H2.
            move /eqP in H2. lia. destruct H5. 
            subst a1;elim H6;auto. exact.  }
            lia. }
           { simpl. rewrite Hbb1. eapply H0. auto. exact. exact. eauto.
             exact. exact. exact. } 
        } 
           (*greater than case *) 
        { simpl. rewrite Hbb1.
          rewrite <- Heqcall in H4. simpl in H4. 
          rewrite <- Heqcall in H5. simpl in H5.
          move /eqP in Hmb. move /leP in Hle.
          destruct H4;destruct H5. 
          { subst a1;auto. }
          { subst a1;auto. }
          { subst a2. assert (In a1 l0). 
            eapply FOA_aux_asks_subset. eauto.
            assert(a<a1). 
            { eapply Sorted_elim4 with (a0:=a)(x:=a1) in H2. 
              unfold by_sp in H2. move /orP in H2. destruct H2. 
              move /leP in H2. lia. move /andP in H2;destruct H2.
              move /eqP in H2. lia. exact. 
            } 
            lia. 
          }
          { case l0 as [| a0 A'].
            { rewrite FOA_aux_triv in H4. simpl in H4. auto. }
            { destruct (a_eqb a1 a0) eqn: Hbb0. 
              { move /eqP in Hbb0. subst a0. eapply FOA_aux_top_ask_fair0.
                simpl. intros. destruct H7. subst m. simpl. lia. auto. eauto. 
                simpl. eapply FOA_QM_ge_bqb with (a1:=a1)(A:=(a1::A'))(a2:=a2) in H4 . 
                simpl in H4. lia. intros. destruct H7. subst m. simpl. lia. auto.
                eauto. eauto. all:exact. 
              }
              { eapply H1. 
                intros. destruct H7. subst m. simpl. lia. auto.
                eauto. eauto. eauto. eauto. eauto. exact. exact. 
                move /eqP in Hbb0. exact.
              } 
            } 
          } 
        } 
      } 
    } 
  } 
} 
Qed.

(*This (FOA_asks_fair) is the main lemma which prove that FOA is fair on asks*)
Lemma FOA_asks_fair (M: list fill_type)(A: list Ask)(a1 a2:Ask)
(NZT:(forall m, In m M -> (tq m) > 0) )(NDA:NoDup A):
Sorted by_sp A ->  
a1<a2 -> 
In a1 (asks_of (FOA M A)) -> In a2 (asks_of (FOA M A))
-> ttqa (FOA M A) a1 = sq a1.
Proof. { unfold FOA. intros. case A as [ |a A' ] eqn: HA.
          { intros. rewrite FOA_aux_triv in H1;simpl in H1;elim H1. }
          { intros.  
          eapply FOA_aux_asks_fair_t with (t:=0)(a:=a)(M:=M)(A:=A')(a2:=a2) in H1.
           destruct H1. assert((a1=a)\/(a1<>a)). eauto. destruct H4.
            { apply H1 in H4. lia. }
            { apply H3 in H4. lia. }
            all:auto. }} Qed.

(*################################################################################*)

(*Lemmas: All matchable in FOA *)

(*################################################################################*)

Lemma FOA_aux_matchable_t (M: list fill_type)(A: list Ask)(a:Ask)(t:nat)
(NZT:(forall m, In m M -> (tq m) > 0) )(NDA:NoDup A) 
(Hanti: antisymmetric by_sp):
Sorted by_sp (a::A) -> 
Sorted m_sp M -> 
All_matchable M -> 
(asks_of M) [<=] (a::A) ->
(forall a0, ttqa M a0 <= sq a0) -> 
(ttqa M a <= sq a - t) ->  
All_matchable (FOA_aux M (a::A) t).

Proof. { funelim ((FOA_aux M (a::A) t)).
+ intros. simp FOA_aux. 
+ unfold All_matchable. intros. 
destruct (Nat.eqb (tq f) (sq a - t)) eqn: Heq. (*EQ case*)
   { rewrite <- Heqcall in H8.
     simpl in H8. destruct H8.  
      { subst m. simpl. assert (In (ask_of f) (a::l0)). (*EQ: Base case *)
        apply H5. simpl. left. auto. assert (In f (f::l)). auto. 
        specialize (H4 f). apply H4 in H9. assert (ask_of f >= a).  
        eapply Sorted_elim2 with (x:=ask_of f) in H2. unfold by_sp in H2.
        move /orP in H2. destruct H2.
        { move /leP in H2. exact. }
        { move /andP in H2. destruct H2. move /eqP in H2. lia. }
        auto. exact. lia. }
      { case l0 as [|a0 A'] eqn: HB. (*EQ: IH case*)
        { rewrite FOA_aux_triv in H8. inversion H8. } 
        { revert H8.
          eapply H. 
          { auto. } 
          { eauto. } 
          { auto. } 
          { auto. }
          { auto. }
          { eauto. }
          { eauto. } 
          { eauto. }
          { move /eqP in Heq. simpl in H7. 
            destruct (a_eqb a (ask_of f)) eqn: Hbm.
            { assert (ttqa l a = 0). lia. 
              assert(~In a (asks_of l)).
              eapply ttqa_intro in H8. auto. auto.
              revert H5. unfold "[<=]". intros. simpl in H5. 
              specialize (H5 a1). destruct H5. right. auto.
              subst a. elim H9. auto. simpl. auto. 
            } 
            { move /eqP in Hbm. assert (In a (asks_of l) 
             \/ ~In a (asks_of l)). eauto.
             destruct H8. 
             { simpl in H5. 
               eapply Sorted_subset with (a1:=(ask_of f))(a2:=a)
               (l2:=(a0::A'))(l1:=(asks_of l))(lr:=by_sp) in H5.
               assert (a=(ask_of f)). apply Hanti. apply /andP.
               destruct H5. auto.
               subst a. elim Hbm.
               auto. apply by_sp_P. apply by_sp_refl. 
               eapply m_sp_and_by_sp in H3. simpl in H3;auto. auto. 
               simpl. right;auto. }
             { simpl in H5. 
               eapply Subset_elim with (a1:=(ask_of f))(a2:=a)(l2:=(a0::A'))
               in H5. eauto. eauto. } 
            } 
          }
         { simpl in H6. intros. specialize (H6 a1). 
           destruct (a_eqb a1 (ask_of f)).
           lia. lia. 
         }
         { simpl in H6. specialize (H6 a0). destruct (a_eqb a0 (ask_of f)).
           lia. lia. 
         } 
       }
     }
   }
   { rewrite <- Heqcall in H8. 
     destruct (Nat.leb (tq f) (sq a - t)) eqn: Hle. 
     { simpl in H8. destruct H8.    (*LT case*)  
        { subst m. simpl. assert (In (ask_of f) (a::l0)). (*LT: Base case*)
          apply H5. simpl. left. auto. assert (In f (f::l)). auto. 
          specialize (H4 f). apply H4 in H9. assert (ask_of f >= a).  
          eapply Sorted_elim2 with (x:=ask_of f) in H2. unfold by_sp in H2.
          move /orP in H2. destruct H2.
          { move /leP in H2. exact. }
          { move /andP in H2. destruct H2. move /eqP in H2. lia. }
          auto. exact. lia. 
        }
        (*LT: IH case*)
        { eapply H0. 
          all: try auto; eauto.
          intros.
          specialize (H6 a0). simpl in H6. destruct (a_eqb a0 (ask_of f)). 
          lia. lia. simpl in H7. 
          destruct (a_eqb a (ask_of f)) eqn: Hbm. 
          { move /leP in Hle.  lia. }
          { move /eqP in Hbm. 
            assert (In a (asks_of l) \/ ~In a (asks_of l)).
            eauto. destruct H9. 
            { simpl in H5. 
              eapply Sorted_subset with (a1:=(ask_of f))(a2:=a)
              (l2:=(l0))(l1:=(asks_of l))(lr:=by_sp) in H5.
              assert (a=(ask_of f)). apply Hanti. apply /andP.
              destruct H5. auto. subst a. elim Hbm.
              auto. apply by_sp_P. apply by_sp_refl. 
              eapply m_sp_and_by_sp in H3. simpl;auto. auto. 
              simpl. right;auto. 
            }
            { eapply  ttqa_elim in H9. lia. } 
          } 
        }
      }
      { simpl in H8. destruct H8.  
      (*GT case*) 
        { subst m. simpl. assert (In (ask_of f) (a::l0)). (*GT: Base case*)
          apply H5. simpl. left. auto. assert (In f (f::l)). auto. 
          specialize (H4 f). apply H4 in H9. assert (ask_of f >= a).  
          eapply Sorted_elim2 with (x:=ask_of f) in H2. 
          unfold by_sp in H2.
          move /orP in H2. destruct H2.
          { move /leP in H2. exact. }
          { move /andP in H2. destruct H2. move /eqP in H2. lia. }
          auto. exact. lia. 
        }
        { case l0 as [|a0 A'] eqn: HB.  (*GT: IH case*)
          { rewrite FOA_aux_triv in H8. inversion H8. }
          { eapply H1 in H8. 
            all: try auto. simpl. intros. destruct H9. subst m0.
            simpl. move /leP in Hle. lia. auto. eauto. eauto. 
            revert H3. constructor. eauto. intros.  simpl. 
            eapply Sorted_elim2  with (x0:=x) in H3. unfold m_sp in H3.
            unfold m_sp. simpl. exact. eauto. eauto. 
            unfold All_matchable. simpl. intros.
            destruct H9. subst m0. simpl. eauto. eauto. simpl. 
            move /leP in Hle. simpl in H7. 
            destruct (a_eqb a (ask_of f)) eqn: Hbm.
            move /eqP in Heq. lia. move /eqP in Hbm. 
            assert (In a (asks_of l) \/ ~In a (asks_of l)). eauto.
            destruct H9. 
            { simpl in H5. 
              eapply Sorted_subset with (a1:=(ask_of f))(a2:=a)
              (l2:=(a0::A'))(l1:=(asks_of l))(lr:=by_sp) in H5.
              assert (a=(ask_of f)). apply Hanti. apply /andP.
              destruct H5. auto. subst a. elim Hbm.
              auto. apply by_sp_P. apply by_sp_refl. 
              eapply m_sp_and_by_sp in H3. simpl;auto. auto. 
              simpl. right;auto. 
            }
            { simpl in H5.
              eapply Subset_elim0 with (a1:=(ask_of f))(a2:=a)
              (l2:=(a0::A')) in H5. eauto. eauto. eauto. 
            }
           intros.  simpl. specialize (H6 a1). simpl in H6. 
           destruct (a_eqb a1 (ask_of f)).
           lia. exact H6. simpl.  specialize (H6 a0). simpl in H6.
           destruct (a_eqb a0 (ask_of f)). lia. lia. 
         } 
       } 
     }
  }
}
Qed.


Lemma FOA_matchable (M: list fill_type)(A: list Ask)
(NZT:(forall m, In m M -> (tq m) > 0) )
(NDA:NoDup A) (Hanti: antisymmetric by_sp):
Sorted by_sp A -> 
Sorted m_sp M -> 
All_matchable M -> 
(asks_of M) [<=] A ->
(forall a0, ttqa M a0 <= sq a0) -> 
All_matchable (FOA M A).
Proof. unfold FOA. intros. 
case A eqn:HA. rewrite FOA_aux_triv. auto. intros.
eapply FOA_aux_matchable_t with (t:=0)(a:=a)(A:=l).
all: auto. eauto. specialize (H3 a);lia. Qed.

(*##########################IR M -> IR FOA#########################*)

Lemma FOA_aux_IR_t (M: list fill_type)(A: list Ask)(a:Ask)(t:nat)
(NZT:(forall m, In m M -> (tq m) > 0) )(NDA:NoDup A) 
(Hanti: antisymmetric by_sp):
Sorted by_sp (a::A) -> 
Sorted m_sp M -> 
Is_IR M -> 
(asks_of M) [<=] (a::A) ->
(forall a0, ttqa M a0 <= sq a0) -> 
(ttqa M a <= sq a - t) ->  
Is_IR (FOA_aux M (a::A) t).

Proof. { funelim ((FOA_aux M (a::A) t)).
+ intros. simp FOA_aux. 
+ unfold Is_IR. intros. 
destruct (Nat.eqb (tq f) (sq a - t)) eqn: Heq. (*EQ case*)
   { rewrite <- Heqcall in H8.
     simpl in H8. destruct H8.  
      { subst m. unfold rational.
       simpl.  assert (In (ask_of f) (a::l0)). (*EQ: Base case *)
        apply H5. simpl. left. auto. assert (In f (f::l)). auto. 
        specialize (H4 f). apply H4 in H9. assert (ask_of f >= a).  
        eapply Sorted_elim2 with (x:=ask_of f) in H2. unfold by_sp in H2.
        move /orP in H2. destruct H2.
        { move /leP in H2. exact. }
        { move /andP in H2. destruct H2. move /eqP in H2. lia. }
        auto. exact. unfold rational in H9. lia. }
      { case l0 as [|a0 A'] eqn: HB. (*EQ: IH case*)
        { rewrite FOA_aux_triv in H8. inversion H8. } 
        { revert H8.
          eapply H. 
          { auto. } 
          { eauto. } 
          { auto. } 
          { auto. }
          { auto. }
          { eauto. }
          { eauto. } 
          { eauto. }
          { move /eqP in Heq. simpl in H7. 
            destruct (a_eqb a (ask_of f)) eqn: Hbm.
            { assert (ttqa l a = 0). lia. 
              assert(~In a (asks_of l)).
              eapply ttqa_intro in H8. auto. auto.
              revert H5. unfold "[<=]". intros. simpl in H5. 
              specialize (H5 a1). destruct H5. right. auto.
              subst a. elim H9. auto. simpl. auto. 
            } 
            { move /eqP in Hbm. assert (In a (asks_of l) 
             \/ ~In a (asks_of l)). eauto.
             destruct H8. 
             { simpl in H5. 
               eapply Sorted_subset with (a1:=(ask_of f))(a2:=a)
               (l2:=(a0::A'))(l1:=(asks_of l))(lr:=by_sp) in H5.
               assert (a=(ask_of f)). apply Hanti. apply /andP.
               destruct H5. auto.
               subst a. elim Hbm.
               auto. apply by_sp_P. apply by_sp_refl. 
               eapply m_sp_and_by_sp in H3. simpl in H3;auto. auto. 
               simpl. right;auto. }
             { simpl in H5. 
               eapply Subset_elim with (a1:=(ask_of f))(a2:=a)(l2:=(a0::A'))
               in H5. eauto. eauto. } 
            } 
          }
         { simpl in H6. intros. specialize (H6 a1). 
           destruct (a_eqb a1 (ask_of f)).
           lia. lia. 
         }
         { simpl in H6. specialize (H6 a0). destruct (a_eqb a0 (ask_of f)).
           lia. lia. 
         } 
       }
     }
   }
   { rewrite <- Heqcall in H8. 
     destruct (Nat.leb (tq f) (sq a - t)) eqn: Hle. 
     { simpl in H8. destruct H8.    (*LT case*)  
        { subst m. simpl. assert (In (ask_of f) (a::l0)). (*LT: Base case*)
          apply H5. simpl. left. auto. assert (In f (f::l)). auto. 
          specialize (H4 f). apply H4 in H9. assert (ask_of f >= a).  
          eapply Sorted_elim2 with (x:=ask_of f) in H2. unfold by_sp in H2.
          move /orP in H2. destruct H2.
          { move /leP in H2. exact. }
          { move /andP in H2. destruct H2. move /eqP in H2. lia. }
          auto. exact. 
          unfold rational in H9. unfold rational. simpl. lia. 
        }
        (*LT: IH case*)
        { eapply H0. 
          all: try auto; eauto.
          intros.
          specialize (H6 a0). simpl in H6. destruct (a_eqb a0 (ask_of f)). 
          lia. lia. simpl in H7. 
          destruct (a_eqb a (ask_of f)) eqn: Hbm. 
          { move /leP in Hle.  lia. }
          { move /eqP in Hbm. 
            assert (In a (asks_of l) \/ ~In a (asks_of l)).
            eauto. destruct H9. 
            { simpl in H5. 
              eapply Sorted_subset with (a1:=(ask_of f))(a2:=a)
              (l2:=(l0))(l1:=(asks_of l))(lr:=by_sp) in H5.
              assert (a=(ask_of f)). apply Hanti. apply /andP.
              destruct H5. auto. subst a. elim Hbm.
              auto. apply by_sp_P. apply by_sp_refl. 
              eapply m_sp_and_by_sp in H3. simpl;auto. auto. 
              simpl. right;auto. 
            }
            { eapply  ttqa_elim in H9. lia. } 
          } 
        }
      }
      { simpl in H8. destruct H8.  
      (*GT case*) 
        { subst m. simpl. assert (In (ask_of f) (a::l0)). (*GT: Base case*)
          apply H5. simpl. left. auto. assert (In f (f::l)). auto. 
          specialize (H4 f). apply H4 in H9. assert (ask_of f >= a).  
          eapply Sorted_elim2 with (x:=ask_of f) in H2. 
          unfold by_sp in H2.
          move /orP in H2. destruct H2.
          { move /leP in H2. exact. }
          { move /andP in H2. destruct H2. move /eqP in H2. lia. }
          auto. exact. unfold rational in H9. unfold rational. simpl. lia. 
        }
        { case l0 as [|a0 A'] eqn: HB.  (*GT: IH case*)
          { rewrite FOA_aux_triv in H8. inversion H8. }
          { eapply H1 in H8. 
            all: try auto.
            { simpl. intros. destruct H9. subst m0.
            simpl. move /leP in Hle. lia. auto. }
            { eauto. }
            { eauto. } 
            { revert H3. constructor. eauto. intros.  simpl. 
            eapply Sorted_elim2  with (x0:=x) in H3. unfold m_sp in H3.
            unfold m_sp. simpl. exact. eauto. eauto. } 
            { unfold Is_IR. simpl. intros.
            destruct H9. subst m0. unfold rational. 
            simpl. apply H4. auto. apply H4. eauto. }
            { 
            simpl. 
            move /leP in Hle. simpl in H7. 
            destruct (a_eqb a (ask_of f)) eqn: Hbm.
            move /eqP in Heq. lia. move /eqP in Hbm. 
            assert (In a (asks_of l) \/ ~In a (asks_of l)). eauto.
            destruct H9. 
            { simpl in H5. 
              eapply Sorted_subset with (a1:=(ask_of f))(a2:=a)
              (l2:=(a0::A'))(l1:=(asks_of l))(lr:=by_sp) in H5.
              assert (a=(ask_of f)). apply Hanti. apply /andP.
              destruct H5. auto. subst a. elim Hbm.
              auto. apply by_sp_P. apply by_sp_refl. 
              eapply m_sp_and_by_sp in H3. simpl;auto. auto. 
              simpl. right;auto. 
            }
            { simpl in H5.
              eapply Subset_elim0 with (a1:=(ask_of f))(a2:=a)
              (l2:=(a0::A')) in H5. eauto. eauto. eauto. 
            }
           }
           { eauto. intros.  simpl. specialize (H6 a1). simpl in H6. 
           destruct (a_eqb a1 (ask_of f)).
           lia. exact H6. }
           { simpl.  specialize (H6 a0). simpl in H6.
           destruct (a_eqb a0 (ask_of f)). lia. lia. } 
         } 
       } 
     }
  }
}
Qed.


Lemma FOA_IR (M: list fill_type)(A: list Ask)
(NZT:(forall m, In m M -> (tq m) > 0) )
(NDA:NoDup A) (Hanti: antisymmetric by_sp):
Sorted by_sp A -> 
Sorted m_sp M -> 
Is_IR M -> 
(asks_of M) [<=] A ->
(forall a0, ttqa M a0 <= sq a0) -> 
Is_IR (FOA M A).
Proof. unfold FOA. intros. 
case A eqn:HA. rewrite FOA_aux_triv. unfold Is_IR.
intros. elim H4.
eapply FOA_aux_IR_t with (t:=0)(a:=a)(A:=l).
all: auto. eauto. specialize (H3 a);lia. Qed.




(*####################################################################*)

(*Uniform FOA*)

(*####################################################################*)

Lemma FOA_uniform (M:list fill_type)(A: list Ask):
Uniform M -> Uniform (FOA M A).
Proof. unfold Uniform. intros.
assert(trade_prices_of (FOA M A) [<=] trade_prices_of M).
apply FOA_aux_tp_subset. eauto. Qed.


(*####################################################################*)

(*Corrolary: Total traded quantity of FOA M B is same as M *)

(*####################################################################*)
Lemma FOA_size (M: list fill_type)(B: list Bid)(A:list Ask)
(NDA:NoDup A)(NDB:NoDup B) (NZT: forall m : fill_type, In m M -> tq m > 0): 
matching_in B A M ->  QM(M)=QM(FOA M A).
Proof. unfold FOA. intros. destruct H. destruct H.
destruct H0. destruct H1. 
rewrite <- QM_equal_QMb with (M:=M)(B:=B).
rewrite <- QM_equal_QMb with (M:=(FOA_aux M A 0))(B:=B).
eapply QMb_equal_QMb with (M1:= M) (M2:=(FOA_aux M A 0)).
intros. eapply FOA_aux_bids_invariant_t.
auto. cut (QM M <=  QA A). lia.
rewrite <- QM_equal_QMa with (A:=A).
eapply fill_size_vs_ask_size.
all:auto. intros. specialize (H3 a). 
assert((In a (asks_of M))\/~In a (asks_of M)). 
eauto. destruct H5. apply H3 in H5. auto.
apply ttqa_elim in H5. lia. 
assert((bids_of (FOA_aux M A 0)) [<=] (bids_of M)).
apply FOA_subA. eauto. Qed.

(*####################Used in compositions #########################*)

Lemma FOA_bids_M_subset_bids_FOA (M: list fill_type)(A: list Ask)(NDA:NoDup A)
(NZT: forall m : fill_type, In m M -> tq m > 0): 
(forall a : Ask, In a (asks_of M) -> ttqa M a <= sq a) ->
asks_of M [<=]A ->
bids_of M [<=] bids_of (FOA M A).
Proof. 
unfold FOA. intros. 
assert(QA A>=QM M).
rewrite <- QM_equal_QMa with (A:=A).
eapply fill_size_vs_ask_size.
all:auto. intros. eauto.
apply ttqb_equal_implies_subet. auto.
intros.
apply FOA_bids_invariant with (M:=M)(A:=A). auto. lia. Qed.



(*##########################################################################*)

(*Lemmas: Total traded quantity for each bids and asks in FOA is less than 
their limit quantity *)

(*#######################################################################*)
Lemma FOA_aux_ttqa_top_t (M: list fill_type)(B: list Bid)(A:list Ask)
(t:nat)(a:Ask)(NDA:NoDup (a::A)): 
ttqa (FOA_aux M (a::A) t) a <= sq a - t.
Proof. {
revert t. induction M as [ | m M'].
{ intro. simp FOA_aux. simpl;lia. }
{ intro. simp FOA_aux.
  destruct (Nat.eqb (tq m) (sq a - t)) eqn:Heq.
  { move /eqP in Heq. simpl. replace (a_eqb a a) with true.
    cut(ttqa (FOA_aux M' A 0) a = 0). lia.
    assert(~In a A). eauto. assert(asks_of ((FOA_aux M' A 0)) [<=] A).
    eapply FOA_aux_asks_subset. assert (~In a (asks_of (FOA_aux M' A 0))).
    eauto. eapply ttqa_elim in H1. exact. auto. 
  }
  { destruct (Nat.leb (tq m) (sq a - t)) eqn:Hle.
    {  simpl. replace (a_eqb a a) with true.
       move /leP in Hle.
       cut(ttqa (FOA_aux M' (a :: A) (t + tq m)) a <= sq a - (t+tq m)).
       lia. eapply IHM'. auto.
    }
    { simpl.
      replace (a_eqb a a) with true.
      cut(ttqa
      (FOA_aux
      ({|
       bid_of := bid_of m;
       ask_of := ask_of m;
       tq := tq m - (sq a - t);
       tp := tp m 
      |} :: M') A 0) a = 0). lia.
      assert(~In a A). eauto. 
      assert(asks_of ((FOA_aux
      ({|
       bid_of := bid_of m;
       ask_of := ask_of m;
       tq := tq m - (sq a - t);
       tp := tp m |} :: M') A 0)) [<=] A).
      eapply FOA_aux_asks_subset. assert (~In a (asks_of (FOA_aux
      ({|
       bid_of := bid_of m;
       ask_of := ask_of m;
       tq := tq m - (sq a - t);
       tp := tp m |} :: M') A 0))).
      eauto. eapply ttqa_elim in H1. exact. auto.
    }
   }
 } 
}Qed. 
  
 
Lemma FOA_aux_ttqa_top0 (M: list fill_type)(A: list Ask)
(B:list Bid)(a:Ask)(NDA:NoDup (a::A)): 
ttqa (FOA_aux M (a::A) 0) a <= sq a.
Proof. cut(ttqa (FOA_aux M (a :: A) 0) a <= sq a - 0). lia.
eapply FOA_aux_ttqa_top_t. eauto. exact. Qed.

Lemma FOA_aux_ttqa_t (M: list fill_type)(B: list Bid)(A:list Ask)(t:nat)(a a1:Ask)
(NDA:NoDup (a::A)): 
(a1=a -> ttqa (FOA_aux M (a::A) t) a1 <= sq a1 - t)/\
(a1<>a -> ttqa (FOA_aux M (a::A) t) a1 <= sq a1). 
Proof.
revert a1. funelim (FOA_aux M (a::A) t). 
{ split;intros;simp FOA_aux;simpl;lia. }
{ intros. destruct (a_eqb a1 a ) eqn: Hbb1. 
  { move /eqP in Hbb1. subst a1. split.
    intros. eapply FOA_aux_ttqa_top_t. auto. eauto.
    intros. elim H2. auto.   
  }
  { split;intros. 
    { subst a1. move /eqP in Hbb1. elim Hbb1. auto. }
    { rewrite<- Heqcall. 
      destruct (Nat.eqb (tq f) (sq a - t)) eqn:Hmb. (*EQ case when b1<>b *)
      { simpl. rewrite Hbb1. case l0 as [|a0 A'] eqn:Hl0. 
        rewrite FOA_aux_triv. simpl;lia.
        destruct (a_eqb a1 a0 ) eqn: Hb0b1.
        { move /eqP in Hb0b1. subst a0. 
          assert(ttqa (FOA_aux l (a1 :: A') 0) a1 <= sq a1 - 0). eapply H.
          all:try auto. eauto. lia. 
        }
        { eapply H. auto. auto. eauto. auto.
          auto. move /eqP in Hb0b1;auto.
        }
      }
      { destruct (Nat.leb (tq f) (sq a - t)) eqn: Hle.
           (*Less than case *) 
        { simpl. rewrite Hbb1.
          eapply H0. auto. auto. simpl. auto.
        }
        { case l0 as [|a0 A'] eqn:Hl0. 
          rewrite FOA_aux_triv. simpl. rewrite Hbb1. lia.
          destruct (a_eqb a1 a0 ) eqn: Hb0b1.
          {
          simpl. rewrite Hbb1.
          move /eqP in Hb0b1. subst a1. 
          assert(ttqa
          (FOA_aux
          ({|
             bid_of := bid_of f;
             ask_of := ask_of f;
             tq := tq f - (sq a - t);
             tp := tp f 
            |} :: l) (a0 :: A') 0) a0 <= sq a0 - 0). eapply H1.
          all:try auto. eauto. lia.
          }
          {
           simpl. rewrite Hbb1. 
           eapply H1. all:try auto. eauto. 
           move /eqP in Hb0b1;auto. 
          }
        }
      }
    }
  }
} Qed.


Lemma FOA_ttqa (M: list fill_type)(B: list Bid)(A:list Ask)(a:Ask)(NDA:NoDup A): 
matching_in B A M-> (ttqa (FOA M A)) a <= sq a. 
Proof. unfold FOA. intros.
     destruct H. destruct H0. destruct H.
     destruct H2.
     case A as [| a0 A'] eqn: HA.
     rewrite FOA_aux_triv. simpl;lia.
     destruct (a_eqb a0 a) eqn: Hbb0.
     move /eqP in Hbb0.
     subst a0.
     eapply FOA_aux_ttqa_top0.
     eauto. eauto.
     eapply FOA_aux_ttqa_t.
     auto. eauto. move /eqP in Hbb0. auto. 
     Qed.

Lemma FOA_ttqb (M: list fill_type)(B: list Bid)(A:list Ask)(b:Bid)
(NDA:NoDup A)(NDB:NoDup B) (NZT:(forall m, In m M -> (tq m) > 0)): 
matching_in B A M -> (ttqb (FOA M A)) b <= bq b.
Proof.
     unfold FOA. intros.
     destruct H. destruct H0. destruct H.
     destruct H2.
     assert(ttqb M b = ttqb (FOA_aux M A 0) b).
     eapply FOA_bids_invariant with (M:=M)(A:=A)(b:=b).
     auto.
     rewrite <- QM_equal_QMa with (A:=A).
     eapply fill_size_vs_ask_size.
     all:auto. intros. specialize (H3 a). 
     assert((In a (asks_of M))\/~In a (asks_of M)). 
     eauto. destruct H5. apply H3 in H5. auto.
     apply ttqa_elim in H5. lia. 
     rewrite <- H4. specialize (H2 b). 
     assert((In b (bids_of M))\/~In b (bids_of M)). 
     eauto. destruct H5. apply H2 in H5. auto.
     apply ttqb_elim in H5. lia. Qed.
 



(******************FOB_NZT*************************)

Lemma FOA_aux_NZT (M: list fill_type)(A:list Ask)(t:nat)(a:Ask)
(NZT:(forall m, In m M -> (tq m) > 0))(NDA:NoDup (a::A))
(NZA:(forall a0, In a0 (a::A) -> (sq a0) > 0))
:
(sq a) > t-> (forall m, In m (FOA_aux M (a::A) t) -> (tq m) > 0).
Proof. { funelim ((FOA_aux M (a::A) t)).
+ intros. simp FOA_aux in H0. 
+ intros. rewrite <- Heqcall in H3. 
destruct (Nat.eqb (tq f) (sq a - t)) eqn: Heq.
{ simpl in H3. destruct H3. subst m. simpl. lia.
  case l0 as [|a0 A'] eqn:Hl0. rewrite FOA_aux_triv in H3. 
  elim H3. apply H in H3. all:auto. eauto.
}
{ destruct (Nat.leb (tq f) (sq a - t)) eqn: Hle.
  { simpl in H3. destruct H3. subst m. simpl. apply NZT.
    auto. apply H0 in H3. all:auto. move /leP in Hle.
    move /eqP in Heq.
    lia.
  }
{ simpl in H3. destruct H3. subst m. simpl. lia.
  case l0 as [|a0 A'] eqn:Hl0. rewrite FOA_aux_triv in H3. 
  elim H3. apply H1 in H3. all:auto.
  intros. simpl in H4. destruct H4. 
  subst m0. simpl. move /leP in Hle.
    move /eqP in Heq.
    lia. eauto. eauto.
} } } Qed.

Lemma FOA_NZT (M: list fill_type)(A:list Ask)
(NZT:(forall m, In m M -> (tq m) > 0))(NDA:NoDup (A))
(NZA:(forall a0, In a0 A -> (sq a0) > 0))
:
(forall m, In m (FOA M A) -> (tq m) > 0).
Proof. unfold FOA. induction A. rewrite FOA_aux_triv.
       simpl. intros. elim H.
       apply FOA_aux_NZT. auto. eauto. eauto. auto. Qed.

(*#############END:NZT FOB######################*)




Lemma FOA_matching (M: list fill_type)(B: list Bid)(A:list Ask)
(NDA:NoDup A)(NDB:NoDup B) (NZT:(forall m, In m M -> (tq m) > 0))
(Hanti: antisymmetric by_sp): 
matching_in B A M -> 
matching_in B A (FOA (sort m_sp M) (sort by_sp A)).
Proof. unfold matching_in. unfold matching.
       intros. assert(bids_of M [<=] B /\ asks_of M [<=] A).
           apply H. destruct H0. 
           
           split.
       { split.
         { apply FOA_matchable. intros. 
           assert(In m M). eapply sort_elim. eauto. auto. eauto.
           auto. eapply sort_correct. apply by_sp_P.
           apply by_sp_P. eapply sort_correct. apply m_sp_P.
           apply m_sp_P. eauto. eauto. intros. 
           assert(ttqa (sort m_sp M) a0 = ttqa M a0).
           eapply ttqa_inv. eauto. rewrite H2.
           assert(In a0 (asks_of M)\/~In a0 (asks_of M)). eauto.
           destruct H3. apply H. auto. apply ttqa_elim in H3. lia.
         }
         split.
         {
          intros. apply FOA_ttqb with (B:=B).
           eauto. eauto. eauto. assert(perm M (sort m_sp M) ). eauto.
           assert(perm A (sort by_sp A)). eauto.
           eapply match_inv with (A':=(sort by_sp A)) (M':=(sort m_sp M))(B':=B) in H3.
           auto. eauto. eauto. apply H.
         }
         {
          intros. apply FOA_ttqa with (B:=B).
           eauto. assert(matching_in B A M). auto.
           eapply match_inv with (A':=(sort by_sp A)) (M':=(sort m_sp M))(B':=B) in H3.
           auto. eauto. auto. eauto.
         } }
      {
      split. assert(bids_of (FOA (sort m_sp M) (sort by_sp A))[<=](bids_of (sort m_sp M))). 
      apply FOA_subA. eauto.
      assert(asks_of (FOA (sort m_sp M) (sort by_sp A))[<=](sort by_sp A)).
      eapply FOA_subB. eauto. 
      }
Qed.


         
Theorem FOA_exists_and_correct (M: list fill_type)(B: list Bid)(A:list Ask)
(NDA:NoDup A)(NDB:NoDup B)(NZT:(forall m, In m M -> (tq m) > 0))
(Hanti: antisymmetric by_sp): 
matching_in B A M ->
(exists M', (matching_in B A M')/\(fair_on_asks M' A)/\(QM(M) = QM(M'))).
Proof. exists (FOA (sort m_sp M) (sort by_sp A)).
split. 
     { eapply FOA_matching in H. all:auto. }
split.
     { unfold fair_on_asks. intros.
       assert(Ha:In s (asks_of (FOA (sort m_sp M) (sort by_sp A)))). 
       eapply FOA_aux_more_competative_in.
       eauto. eauto. apply sort_correct. apply by_sp_P.
       apply by_sp_P. eauto. destruct H0. eauto.
       destruct H0. eauto. eauto. split. auto.
       eapply FOA_asks_fair. all:auto. eauto. 
       apply sort_correct. apply by_sp_P.
       apply by_sp_P. eauto. eauto.
     }
     replace (QM(M)) with (QM(sort m_sp M)). eapply FOA_size.
     
     all:eauto. eapply match_inv with (A':=(sort by_sp A)) (M':=(sort m_sp M))(B':=B) in H.
     auto. eauto. eauto. eauto.
Qed.

End Fair_Ask.


