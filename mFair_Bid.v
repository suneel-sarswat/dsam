
(* ------------   Work to be done : organise the hints properly ------------- *)



(* -------------------------------------------------------------------------------------

      This file contains all the important results about fair matching on bids.
      The main result is existance of a fair matching without compromizing its total quantity.

       by_dbp           <===>   order by decreasing bp and increasing time (if bp is same)
       FOB M B          <===>   makes M fair on bids B


Some important results:


Theorem exists_fair_matching :
  matching_in B A M-> 
  (exists M':list fill_type, matching_in B A M' /\ Is_fair M' B A /\ QM(M)= QM(M')).

------------------------------------------------------------------------------------------*)







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


(*Require Export AuctionInvar.*)

Section Fair.
 
Definition fair_on_bids (M: list fill_type)(B: list Bid):=
  (forall b b', In b B /\ In b' B -> b > b' -> In b' (bids_of M) -> 
  (ttqb M b')>0-> 
  (In b (bids_of M)/\(ttqb M b= bq b))).

Definition fair_on_asks (M: list fill_type) (A: list Ask):=
  (forall s s', In s A /\ In s' A -> s < s' -> In s' (asks_of M) ->
  (ttqa M s')>0 -> 
  (In s (asks_of M)/\(ttqa M s= sq s))).

Definition Is_fair (M: list fill_type) (B: list Bid) (A: list Ask) 
  :=  fair_on_asks M A /\ fair_on_bids M B.


(*##################Sorting Criteria for Bids and Matchings for fair ####################*)

Definition by_dbp (b1:Bid) (b2:Bid) :=(Nat.leb b2 b1) ||
((Nat.eqb b2 b1) && (Nat.leb (btime b1)  (btime b2) )).
Lemma comp_triv (bp:nat)(bp0:nat):
~ (Nat.leb bp0 bp) -> (Nat.leb bp bp0).
Proof. revert bp. induction bp0. simpl. intro. eauto. intros. 
 simpl in H. destruct bp. simpl. auto. intros. simpl. eapply IHbp0. auto. Qed.
Lemma by_dbp_P : transitive by_dbp /\ comparable by_dbp.
Proof.  { split.
          { unfold transitive. unfold by_dbp.  
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
          { unfold comparable. unfold by_dbp. intros. move /orP in H.
            assert (~ ((Nat.leb y x))). eauto. apply /orP. left.
            destruct x. destruct y. simpl in H0. simpl in H. simpl.
            apply comp_triv. auto. } } Qed.

                
Lemma by_dbp_refl: reflexive by_dbp.
Proof. unfold reflexive. intros. unfold by_dbp. apply /orP. 
left. apply nat_reflexive.  Qed.


Definition m_dbp (m1:fill_type) (m2:fill_type) := by_dbp (bid_of m1) (bid_of m2).

Lemma m_dbp_P : transitive m_dbp /\ comparable m_dbp.
Proof. { split.
         { unfold transitive. unfold m_dbp. 
           intros. cut (transitive by_dbp). intros. eauto using by_dbp_P. 
            apply by_dbp_P. }
         { unfold comparable.  unfold m_dbp. intros x y H. eapply by_dbp_P. 
           exact.  } } Qed.

Lemma m_dbp_refl: reflexive m_dbp.
Proof. unfold reflexive. intros. unfold m_dbp. unfold by_dbp. 
apply /orP. left. apply nat_reflexive. Qed.

Lemma m_dbp_and_by_dbp (M:list fill_type):
Sorted m_dbp M -> Sorted by_dbp (bids_of M).
Proof. intros. induction M. simpl. constructor. simpl. inversion H.
assert(exists b, b=(bid_of a)). eauto.
destruct H4. rewrite <- H4.
constructor. apply IHM. eauto. intros.
assert (exists m0, (In m0 M)/\(x0=(bid_of m0))).
eapply bids_of_elim. auto.
destruct H6. destruct H6. apply H3 in H6. unfold m_dbp in H6.
subst. auto. Qed.

Hint Resolve m_dbp_P by_dbp_P : core.
Hint Resolve by_dbp_refl m_dbp_refl : core.



(*####################################################################################*)
  
(*----------------  Function to make a matching fair on bids -----------------------*)

(*####################################################################################*)


Equations FOB_aux (M:list fill_type) (B: list Bid) (t: nat): 
(list fill_type) by wf (|M| + |B|):=
FOB_aux nil _ _ := nil;
FOB_aux _ nil _:= nil;
FOB_aux (m::M') (b::B') t:=  if (Nat.eqb (tq m) (bq b - t)) then 

(Mk_fill b (ask_of m) (bq b - t) (tp m))::(FOB_aux M' B' 0) 

else (if (Nat.leb (tq m) (bq b - t)) then

(Mk_fill b (ask_of m) (tq m) (tp m)):: (FOB_aux M' (b::B') (t + tq m))

else 

(Mk_fill b (ask_of m) (bq b - t) (tp m)):: 
(FOB_aux ((Mk_fill (bid_of m) (ask_of m) (tq m - (bq b - t)) (tp m))::M') B' 0)).

Next Obligation.
lia. Qed.
Next Obligation.
lia. Qed.

Definition FOB (M:list fill_type) (B: list Bid) := FOB_aux M B 0.


(*################################################################################*)
(*Lemma on subsets: The list of Bids of FOB is subset of B 
  and the Asks are subset of input M*)
(*################################################################################*)

Lemma FOB_aux_bids_subset (M: list fill_type) (B:list Bid)(t:nat) :
bids_of (FOB_aux M B t) [<=] B.
Proof. apply FOB_aux_elim. all: auto.
{
 intros. destruct (Nat.eqb (tq f) (bq b - t0)) eqn: Hfb. 
 { simpl. cut (bids_of (FOB_aux l l0 0) [<=] l0). auto. exact H. }
 { destruct (Nat.leb (tq f) (bq b - t0)) eqn: Hbf. 
 { simpl. eapply subset_elim1. apply H0. }
 {  simpl. eapply subset_elim2 with (a:=b). exact H1. }
 } 
}
Qed.

           
Lemma FOB_aux_asks_subset (M: list fill_type) (B:list Bid) (t:nat):
asks_of (FOB_aux M B t) [<=] asks_of M.
Proof. apply FOB_aux_elim. all: auto.
{
 intros. destruct (Nat.eqb (tq f) (bq b -t0)) eqn: Hfb. 
 { simpl. cut (asks_of (FOB_aux l l0 0) [<=] asks_of l). 
   auto. move /eqP in Hfb. 
   assert ((tq f - (bq b - t0)) =0). lia.  exact H. 
 }
 { destruct (Nat.leb (tq f) (bq b - t0)) eqn: Hbf. 
   { simpl. eapply subset_elim2. apply H0. }
   { simpl. simpl in H1. eapply subset_elim1. exact H1. }
 }
}
Qed.

Lemma FOB_subA (M: list fill_type)(B: list Bid): asks_of (FOB M B) [<=] asks_of M.
Proof. { unfold FOB. apply FOB_aux_asks_subset. } Qed.
Lemma FOB_subB (M:list fill_type) (B:list Bid): bids_of (FOB M B) [<=] B.
Proof. { unfold FOB. apply FOB_aux_bids_subset. } Qed. 

(*################################################################################*)
(*Lemmas: Total traded quantity *)

(*################################################################################*)



(*This lemma (fob_asks_invariant) ensures that the total traded quantity for each ask in FOB is equal to it's  traded quantity in the input atching M. With this it is starightforward that the total traded quantity of an ask in FOB is less than or equal to it's  ask quantity, since M is a matching. This lemma is also useful to ensures that the asks are not changed during fair on bids. This is useful to prove that during composition of FOB to FOA functions the fairness property of FOA remains invariant. This lemaa is also useful to show that the total traded quantity of FOB is same as input M. *)

Lemma FOB_aux_asks_invariant_t (M:list fill_type)(B:list Bid)(a:Ask)(t:nat)
(NZT:(forall m, In m M -> (tq m) > 0) ):
QB(B)>=QM(M)+t -> ttqa M a = ttqa (FOB_aux M B t) a.
Proof.
funelim (FOB_aux M B t). all:auto.
+ intros. simpl in H. assert(tq f =0). lia. assert(tq f >0). apply NZT. auto.
rewrite H0 in H1. inversion H1.
+ intros. rewrite <- Heqcall. destruct (Nat.eqb (tq f) (bq b - t)) eqn:Heq0. 
{ simpl. destruct (a_eqb a (ask_of f)) eqn:Ham. 
 cut (ttqa l a = ttqa (FOB_aux l l0 0) a). auto. 
 all: eapply H. all: try (simpl; lia);auto;eauto.
 all: simpl in H2. all:move /eqP in Heq0. lia. lia. }
{ intros. destruct (Nat.leb (tq f) (bq b - t)) eqn: Hle. 
{ simpl. simpl in H2. 
move /leP in Hle. move /eqP in Heq0. destruct (a_eqb a (ask_of f)) eqn:Ham. 
cut( ttqa l a = ttqa (FOB_aux l (b :: l0) (t + tq f)) a). auto.
 eapply H0. all: try (simpl; lia);auto.
eapply H0. all: try (simpl; lia);auto. }
{ simpl. simpl in H2. 
move /leP in Hle. move /eqP in Heq0. 
assert (ttqa (FOB_aux 
      ({|bid_of := bid_of f;
      ask_of := ask_of f;
      tq := tq f - (bq b - t);
      tp := tp f |} :: l) 
      l0 0) a = 
      ttqa ({|bid_of := bid_of f;
      ask_of := ask_of f;
      tq := tq f - (bq b - t);
      tp := tp f |} :: l) a). symmetry. 
      (*Handle this situation in general, try to clean it using ltac*)
 eapply H1. all: try (simpl; lia);auto. 
 { intros. simpl in H3. destruct H3. subst m. simpl. lia. auto. } rewrite H3.
 simpl. destruct (a_eqb a (ask_of f)) eqn:Ham. simpl. lia. lia. } } Qed.


Lemma FOB_asks_invariant (M:list fill_type)(B:list Bid)(a:Ask)
(NZT:(forall m, In m M -> (tq m) > 0) ):
QB(B)>=QM(M) -> ttqa M a = ttqa (FOB M B) a.
Proof. unfold FOB. intros. eapply FOB_aux_asks_invariant_t. auto. lia. Qed.

(*################################################################################*)

(*Lemmas: Fair property *)

(*################################################################################*)

(*In this lemma (fob_aux_top_bid_fair) we first show that the top bid in B is fully traded (trade quantity is total quantity. Note that, for arbitrary value of t, the statement is total quantity minus t. For t=0, the statement of following lemma is same as fully traded*)

Lemma FOB_aux_top_bid_fair (M: list fill_type)(B:list Bid)(b:Bid)(t:nat)
(NZT:(forall m, In m M -> (tq m) > 0) )(NDB:NoDup (b::B)):
QM(M)>=(bq b) - t -> ttqb (FOB_aux M (b::B) t) b = bq b - t.
Proof. 
revert t B b NDB. induction M as [ | m M']. intros.
simp FOB_aux. simpl. simpl in H. lia.
{ intros. simp FOB_aux. destruct (Nat.eqb (tq m) (bq b -t )) eqn: Heq0. 
{ 
simpl.  assert(b_eqb b b = true). eauto. rewrite H0.
cut (ttqb (FOB_aux M' B 0) b = 0). lia.

assert (~In b B). eauto.
 assert (forall t, bids_of (FOB_aux M' B t) [<=] B). intros.
  eapply FOB_aux_bids_subset with (M:=M')(t:=t0)(B:=B).
 assert (forall t, ~In b (bids_of (FOB_aux M' B t))).  intros. specialize (H2 t0).
 eauto. apply ttqb_elim. auto. }
{ intros. destruct (Nat.leb (tq m) (bq b - t)) eqn: Hle. 
{ simpl. assert(b_eqb b b = true). eauto. rewrite H0. 
assert (ttqb (FOB_aux M' (b :: B) (t+tq m)) b = bq b - (t+tq m)).
apply IHM'. auto. exact NDB. simpl in H. move /leP in Hle. lia. 
move /leP in Hle. rewrite H1. lia. }
{ simpl. 
assert(b_eqb b b = true). eauto. rewrite H0. 
cut (ttqb (FOB_aux ({|bid_of := bid_of m;
      ask_of := ask_of m;
      tq := tq m - (bq b - t);
      tp := tp m |} :: M') B 0) b = 0). lia.
assert (~In b B). eauto.
 assert (bids_of (FOB_aux ({|bid_of := bid_of m;
      ask_of := ask_of m;
      tq := tq m - (bq b - t);
      tp := tp m |} :: M') B 0) [<=] B). eapply FOB_aux_bids_subset.
 assert (~In b (bids_of (FOB_aux ({|bid_of := bid_of m;
      ask_of := ask_of m;
      tq := tq m - (bq b - t);
      tp := tp m |} :: M') B 0))).  
 eauto. apply ttqb_elim. auto. }} } Qed.


(*Special case of above lemma for t=0 *)
Lemma FOB_aux_top_bid_fair0 (M: list fill_type)(B:list Bid)(b:Bid)
(NZT:(forall m, In m M -> (tq m) > 0) )(NDB:NoDup (b::B)):
QM(M)>=(bq b)-> ttqb (FOB M (b::B)) b = bq b.
Proof.
unfold FOB.
cut(QM(M)>=(bq b) - 0-> ttqb (FOB_aux M (b::B) 0) b = bq b - 0). lia.
eapply FOB_aux_top_bid_fair with (t:=0)(b:=b)(M:=M). exact. exact. Qed.

(*This lemma ensures that if a less move competitive bid is part of FOB then less competitive 
must be part of matching.*)
Lemma FOB_aux_more_competative_in (M: list fill_type)(B:list Bid)(b1 b2:Bid)(t:nat)
(NZT:(forall m, In m M -> (tq m) > 0) )(NDB:NoDup B):
Sorted by_dbp B ->
b1>b2 -> 
In b1 B ->
In b2 B ->
In b2 (bids_of (FOB_aux M B t))-> 
In b1 (bids_of (FOB_aux M B t)).
Proof. 
funelim (FOB_aux M B t). 
+ intros. simp FOB_aux in H1. 
+ intros. simp FOB_aux in H1.
+ intros. destruct (b_eqb b b1) eqn: Hbb1;destruct (b_eqb b b2) eqn: Hbb2.
{ move /eqP in Hbb1;move /eqP in Hbb2.
  subst b1;subst b2. lia. }
{ move /eqP in Hbb1;subst b1. 
  rewrite <- Heqcall.
  destruct (Nat.eqb (tq f) (bq b - t)) eqn:Heq0.  
  simpl. left;auto.
  destruct (Nat.leb (tq f) (bq b - t)) eqn:Hle.
  simpl. left;auto.
  simpl. left;auto.
}
{ move /eqP in Hbb2;subst b2.
  { eapply Sorted_elim4 with (a:=b)(x:=b1) in H2. 
    unfold by_dbp in H2.
    move /orP in H2. destruct H2. 
    move /leP in H2. lia. move /andP in H2;destruct H2.
    move /eqP in H2. lia. auto. destruct H4.
    subst b1. lia. exact.      
  }
}
{
  destruct H4;destruct H5.
  { subst b. move /eqP in Hbb1. elim Hbb1;auto. } 
  { subst b. move /eqP in Hbb1. elim Hbb1;auto. }
  { subst b. move /eqP in Hbb2. elim Hbb2;auto. }
  { rewrite <- Heqcall. rewrite <- Heqcall in H6.
    destruct (Nat.eqb (tq f) (bq b - t)) eqn: Heq.
    { simpl. simpl in H6. destruct H6.
      { subst b. move /eqP in Hbb2. elim Hbb2;auto. }
      { right. eapply H. auto. all:eauto. }
    }    
    { destruct (Nat.leb (tq f) (bq b - t)) eqn: Hle.
      { simpl. simpl in H6. destruct H6.
        { subst b. move /eqP in Hbb2. elim Hbb2;auto. }
        { right. eapply H0. auto. all:eauto. }
      }
      { simpl. simpl in H6. destruct H6.
        { subst b. move /eqP in Hbb2. elim Hbb2;auto. }
        { right. eapply H1. auto. 
          intros. simpl in H7. destruct H7. subst m.
          simpl. move /eqP in Heq. move /leP in Hle. lia. 
           all:eauto. 
        }
      }
    }
  }    
} Qed.  
    

(*Following lemma (TQ_FM) ensures that if a less competitive bid is part of FOB_aux then 
the total quantity traded in the matching should be more that or equal to more competitive bid*)

Lemma TQ_FM (M: list fill_type)(B:list Bid)(b1 b2:Bid)(t:nat)
(NZT:(forall m, In m M -> (tq m) > 0) )(NDB:NoDup B):
Sorted by_dbp B ->  b1>b2 -> 
In b1 (bids_of (FOB_aux M B t)) -> In b2 (bids_of (FOB_aux M B t))
->  QM(M)>=bq b1 - t.
Proof.  funelim (FOB_aux M B t). 
+ intros. simp FOB_aux in H1. simpl in H1;elim H1.
+ intros. simp FOB_aux in H1. simpl in H1;elim H1.
+ intros. rewrite <- Heqcall in H4. rewrite <- Heqcall in H5.
destruct (Nat.eqb (tq f) (bq b - t)) eqn:Heq0.  
{  (*Case : EQ *)
   simpl in H4. simpl in H5. move /eqP in Heq0. destruct H4;destruct H5. 
   { subst b1. simpl. lia. }
   { subst b1. simpl. lia. }
   { (*this case contradict sorted. Move this into 
     a general result and automate. *)subst b2. assert (In b1 l0). eapply FOB_aux_bids_subset.
     eauto. assert(b>b1). 
     { eapply Sorted_elim4 with (a:=b)(x:=b1) in H2. unfold by_dbp in H2.
     move /orP in H2. destruct H2. move /leP in H2. lia. move /andP in H2;destruct H2.
     move /eqP in H2. lia. auto. }
    lia. } 
   { eapply H in H3. all: try (simpl;lia);auto;eauto. } 
}   (*End Case : EQ*)
{ 
   destruct (Nat.leb (tq f) (bq b - t)) eqn: Hle. 
   { (*Case : Top trade quantity is less than the the top bid  *)
     move /eqP in Heq0. move /leP in Hle. simpl in H4. simpl in H5.
     destruct H4;destruct H5. 
      { subst. inversion H3. lia. lia. }
      { subst b. eapply H0 in H3. all: try (simpl;lia);auto. 
       { case l eqn:Hl.  simp FOB_aux in H5. simp FOB_aux.
         destruct (Nat.eqb (tq f0) (bq b1 - (t + tq f))) eqn:Hfb1. 
         simpl. left. auto. 
         destruct (Nat.leb (tq f0) (bq b1 - (t + tq f))) eqn: Hfble.
         simpl;left;auto. 
         simpl;left;auto.   } 
      }
      { subst b2. assert (In b1 (b::l0)). 
        eapply FOB_aux_bids_subset with (B:=(b::l0)).
        eauto. assert(b>b1). 
        { eapply Sorted_elim4 with (a:=b)(x:=b1) in H2. 
          unfold by_dbp in H2.
          move /orP in H2. destruct H2. 
          move /leP in H2. lia. move /andP in H2;destruct H2.
          move /eqP in H2. lia. destruct H5. subst b. lia. auto. 
        } lia. 
      }
      { eapply H0 with (b1:=b1) in H5. all: try (simpl;lia);auto. } 
   }
   { (*Case : Top trade quantity is more than the the top bid  *)
     move /eqP in Heq0. move /leP in Hle. simpl in H4. simpl in H5.
     destruct H4;destruct H5.
     { subst. inversion H3. lia. lia. }
     { subst b. simpl. lia. }
     { eapply Sorted_elim4 with (a:=b)(x:=b1) in H2. 
       unfold by_dbp in H2.
       move /orP in H2. destruct H2. move /leP in H2. subst b. simpl. lia. 
       move /andP in H2;destruct H2. move /eqP in H2. simpl. subst b. lia. 
       eapply FOB_aux_bids_subset with (B:=(l0)) in H4. exact. 
     }
     { eapply H1 with (b1:=b1) in H5. simpl in H5. all: try (simpl;lia);auto. 
      intros. simpl in H6. destruct H6. subst m. all: try (simpl;lia);auto;eauto. 
     } 
   } 
}   Qed.
      
Lemma FOB_aux_triv (l:list fill_type):
FOB_aux l nil 0 =nil.
Proof. funelim (FOB_aux l nil 0). simp FOB_aux. auto. simp FOB_aux. auto. Qed.

(*Following lemma (fob_aux_bids_fair_t) is the main fair lemma for arbitrary value of t.
  Note that, for t=0 the lemma is fair_on_bids lemma.*)
Lemma FOB_aux_bids_fair_t (M: list fill_type)(B:list Bid)(b b1 b2:Bid)(t:nat)
(NZT:(forall m, In m M -> (tq m) > 0) )(NDB:NoDup (b::B)):
Sorted by_dbp (b::B) ->  
b1>b2 -> 
In b1 (bids_of (FOB_aux M (b::B) t)) -> 
In b2 (bids_of (FOB_aux M (b::B) t)) ->  
(b1=b -> ttqb (FOB_aux M (b::B) t) b1 = bq b1 - t )/\
(b1<>b->ttqb (FOB_aux M (b::B) t) b1 = bq b1 ).
Proof.
funelim (FOB_aux M (b::B) t). auto. 
{ intros. destruct (b_eqb b1 b ) eqn: Hbb1. 
  { move /eqP in Hbb1. subst b. split.
    intros. eapply FOB_aux_top_bid_fair. auto. auto. eapply TQ_FM in H5. 
    all: try (simpl;lia);auto;eauto.  
  }
  { split;intros. 
    { subst b1. move /eqP in Hbb1. auto. }
    { rewrite<- Heqcall. 
      destruct (Nat.eqb (tq f) (bq b - t)) eqn:Hmb. (*EQ case when b1<>b *)
      { simpl. rewrite Hbb1. 
        rewrite<- Heqcall in H4. simpl in H4. 
        rewrite<- Heqcall in H5. simpl in H5. 
        destruct H4;destruct H5. 
        { subst b1;auto. }
        { subst b1;auto. }
        { subst b2. assert (In b1 l0). 
          eapply FOB_aux_bids_subset. eauto.
          assert(b>b1). 
          { eapply Sorted_elim4 with (a:=b)(x:=b1)(lr:=by_dbp) in H2. 
            unfold by_dbp in H2. move /orP in H2. destruct H2. 
            move /leP in H2. lia. move /andP in H2;destruct H2.
            move /eqP in H2. lia. auto.  } 
            lia. }
         { case l0 as [| b0 B'] eqn:Hl0.
             { rewrite FOB_aux_triv in H4. simpl in H4. auto. }
             { destruct (b_eqb b1 b0) eqn: Hbb0. 
                  { move /eqP in Hbb0. subst b0. eapply FOB_aux_top_bid_fair0.
                    auto. eauto. eapply TQ_FM with (b1:=b1)(B:=(b1::B'))(b2:=b2) in H5.
                    lia. auto. eauto. eauto. all:exact. }
                  { eapply H. auto. eauto. auto. auto. eauto. eauto. 
                    exact. exact. move /eqP in Hbb0. exact. } 
             } 
         } 
      }
      { destruct (Nat.leb (tq f) (bq b - t)) eqn: Hle.
           (*Less than case *) 
        { rewrite <- Heqcall in H4. simpl in H4.
          rewrite <- Heqcall in H5. simpl in H5.
          move /eqP in Hmb. move /leP in Hle.
          destruct H4;destruct H5. 
          { subst b1;auto. }
          { subst b1;auto. }
          { subst b2. assert (In b1 (b::l0)). 
            eapply FOB_aux_bids_subset. eauto.
            assert(b>b1). 
            { eapply Sorted_elim4 with (a:=b)(x:=b1)(lr:=by_dbp) in H2. 
            unfold by_dbp in H2. move /orP in H2. destruct H2. 
            move /leP in H2. lia. move /andP in H2;destruct H2.
            move /eqP in H2. lia. destruct H5. 
            subst b1;elim H6;auto. exact.  }
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
          { subst b1;auto. }
          { subst b1;auto. }
          { subst b2. assert (In b1 l0). 
            eapply FOB_aux_bids_subset. eauto.
            assert(b>b1). 
            { eapply Sorted_elim4 with (a:=b)(x:=b1) in H2. 
              unfold by_dbp in H2. move /orP in H2. destruct H2. 
              move /leP in H2. lia. move /andP in H2;destruct H2.
              move /eqP in H2. lia. exact. 
            } 
            lia. 
          }
          { case l0 as [| b0 B'].
            { rewrite FOB_aux_triv in H4. simpl in H4. auto. }
            { destruct (b_eqb b1 b0) eqn: Hbb0. 
              { move /eqP in Hbb0. subst b0. eapply FOB_aux_top_bid_fair0.
                simpl. intros. destruct H7. subst m. simpl. lia. auto. eauto. 
                simpl. eapply TQ_FM with (b1:=b1)(B:=(b1::B'))(b2:=b2) in H4 . 
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

(*This (FOB_bids_fair) is the main lemma which prove that FOB is fair on bids*)
Lemma FOB_bids_fair (M: list fill_type)(B:list Bid)(b1 b2:Bid)
(NZT:(forall m, In m M -> (tq m) > 0) )(NDB:NoDup B):
Sorted by_dbp B ->  
b1>b2 -> 
In b1 (bids_of (FOB M B)) -> In b2 (bids_of (FOB M B))
-> ttqb (FOB M B) b1 = bq b1.
Proof. { unfold FOB. intros. case B as [ |b B' ] eqn: HB.
          { intros. rewrite FOB_aux_triv in H1;simpl in H1;elim H1. }
          { intros.  
          eapply FOB_aux_bids_fair_t with (t:=0)(b:=b)(M:=M)(B:=B')(b2:=b2) in H1.
           destruct H1. assert((b1=b)\/(b1<>b)). eauto. destruct H4.
            { apply H1 in H4. lia. }
            { apply H3 in H4. lia. }
            all:auto. }} Qed.

(*################################################################################*)

(*Lemmas: All matchable in FOB *)

(*################################################################################*)

Lemma FOB_aux_matchable_t (M: list fill_type)(B:list Bid)(b:Bid)(t:nat)
(NZT:(forall m, In m M -> (tq m) > 0) )(NDB:NoDup B) 
(Hanti: antisymmetric by_dbp):
Sorted by_dbp (b::B) -> 
Sorted m_dbp M -> 
All_matchable M -> 
(bids_of M) [<=] (b::B) ->
(forall b0, ttqb M b0 <= bq b0) -> 
(ttqb M b <= bq b - t) ->  
All_matchable (FOB_aux M (b::B) t).

Proof. { funelim ((FOB_aux M (b::B) t)).
+ intros. simp FOB_aux. 
+ unfold All_matchable. intros. 
destruct (Nat.eqb (tq f) (bq b - t)) eqn: Heq. (*EQ case*)
   { rewrite <- Heqcall in H8.
     simpl in H8. destruct H8.  
      { subst m. simpl. assert (In (bid_of f) (b::l0)). (*EQ: Base case *)
        apply H5. simpl. left. auto. assert (In f (f::l)). auto. 
        specialize (H4 f). apply H4 in H9. assert (bid_of f <= b).  
        eapply Sorted_elim2 with (x:=bid_of f) in H2. unfold by_dbp in H2.
        move /orP in H2. destruct H2.
        { move /leP in H2. exact. }
        { move /andP in H2. destruct H2. move /eqP in H2. lia. }
        auto. exact. lia. }
      { case l0 as [|b0 B'] eqn: HB. (*EQ: IH case*)
        { rewrite FOB_aux_triv in H8. inversion H8. } 
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
            destruct (b_eqb b (bid_of f)) eqn: Hbm.
            { assert (ttqb l b = 0). lia. 
              assert(~In b (bids_of l)).
              eapply ttqb_intro in H8. auto. auto.
              revert H5. unfold "[<=]". intros. simpl in H5. 
              specialize (H5 a). destruct H5. right. auto.
              subst a. elim H9. auto. simpl. auto. 
            } 
            { move /eqP in Hbm. assert (In b (bids_of l) 
             \/ ~In b (bids_of l)). eauto.
             destruct H8. 
             { simpl in H5. 
               eapply Sorted_subset with (a1:=(bid_of f))(a2:=b)
               (l2:=(b0::B'))(l1:=(bids_of l))(lr:=by_dbp) in H5.
               assert (b=(bid_of f)). apply Hanti. apply /andP.
               destruct H5. auto.
               subst b. elim Hbm.
               auto. apply by_dbp_P. apply by_dbp_refl. 
               eapply m_dbp_and_by_dbp in H3. simpl in H3;auto. auto. 
               simpl. right;auto. }
             { simpl in H5. 
               eapply Subset_elim with (a1:=(bid_of f))(a2:=b)(l2:=(b0::B'))
               in H5. eauto. eauto. } 
            } 
          }
         { simpl in H6. intros. specialize (H6 b1). 
           destruct (b_eqb b1 (bid_of f)).
           lia. lia. 
         }
         { simpl in H6. specialize (H6 b0). destruct (b_eqb b0 (bid_of f)).
           lia. lia. 
         } 
       }
     }
   }
   { rewrite <- Heqcall in H8. 
     destruct (Nat.leb (tq f) (bq b - t)) eqn: Hle. 
     { simpl in H8. destruct H8.    (*LT case*)  
        { subst m. simpl. assert (In (bid_of f) (b::l0)). (*LT: Base case*)
          apply H5. simpl. left. auto. assert (In f (f::l)). auto. 
          specialize (H4 f). apply H4 in H9. assert (bid_of f <= b).  
          eapply Sorted_elim2 with (x:=bid_of f) in H2. unfold by_dbp in H2.
          move /orP in H2. destruct H2.
          { move /leP in H2. exact. }
          { move /andP in H2. destruct H2. move /eqP in H2. lia. }
          auto. exact. lia. 
        }
        (*LT: IH case*)
        { eapply H0. 
          all: try auto; eauto.
          intros.
          specialize (H6 b0). simpl in H6. destruct (b_eqb b0 (bid_of f)). 
          lia. lia. simpl in H7. 
          destruct (b_eqb b (bid_of f)) eqn: Hbm. 
          { move /leP in Hle.  lia. }
          { move /eqP in Hbm. 
            assert (In b (bids_of l) \/ ~In b (bids_of l)).
            eauto. destruct H9. 
            { simpl in H5. 
              eapply Sorted_subset with (a1:=(bid_of f))(a2:=b)
              (l2:=(l0))(l1:=(bids_of l))(lr:=by_dbp) in H5.
              assert (b=(bid_of f)). apply Hanti. apply /andP.
              destruct H5. auto. subst b. elim Hbm.
              auto. apply by_dbp_P. apply by_dbp_refl. 
              eapply m_dbp_and_by_dbp in H3. simpl;auto. auto. 
              simpl. right;auto. 
            }
            { eapply  ttqb_elim in H9. lia. } 
          } 
        }
      }
      { simpl in H8. destruct H8.  
      (*GT case*) 
        { subst m. simpl. assert (In (bid_of f) (b::l0)). (*GT: Base case*)
          apply H5. simpl. left. auto. assert (In f (f::l)). auto. 
          specialize (H4 f). apply H4 in H9. assert (bid_of f <= b).  
          eapply Sorted_elim2 with (x:=bid_of f) in H2. 
          unfold by_dbp in H2.
          move /orP in H2. destruct H2.
          { move /leP in H2. exact. }
          { move /andP in H2. destruct H2. move /eqP in H2. lia. }
          auto. exact. lia. 
        }
        { case l0 as [|b0 B'] eqn: HB.  (*GT: IH case*)
          { rewrite FOB_aux_triv in H8. inversion H8. }
          { eapply H1 in H8. 
            all: try auto. simpl. intros. destruct H9. subst m0.
            simpl. move /leP in Hle. lia. auto. eauto. eauto. 
            revert H3. constructor. eauto. intros.  simpl. 
            eapply Sorted_elim2  with (x0:=x) in H3. unfold m_dbp in H3.
            unfold m_dbp. simpl. exact. eauto. eauto. 
            unfold All_matchable. simpl. intros.
            destruct H9. subst m0. simpl. eauto. eauto. simpl. 
            move /leP in Hle. simpl in H7. 
            destruct (b_eqb b (bid_of f)) eqn: Hbm.
            move /eqP in Heq. lia. move /eqP in Hbm. 
            assert (In b (bids_of l) \/ ~In b (bids_of l)). eauto.
            destruct H9. 
            { simpl in H5. 
              eapply Sorted_subset with (a1:=(bid_of f))(a2:=b)
              (l2:=(b0::B'))(l1:=(bids_of l))(lr:=by_dbp) in H5.
              assert (b=(bid_of f)). apply Hanti. apply /andP.
              destruct H5. auto. subst b. elim Hbm.
              auto. apply by_dbp_P. apply by_dbp_refl. 
              eapply m_dbp_and_by_dbp in H3. simpl;auto. auto. 
              simpl. right;auto. 
            }
            { simpl in H5.
              eapply Subset_elim0 with (a1:=(bid_of f))(a2:=b)
              (l2:=(b0::B')) in H5. eauto. eauto. eauto. 
            }
           intros.  simpl. specialize (H6 b1). simpl in H6. 
           destruct (b_eqb b1 (bid_of f)).
           lia. exact H6. simpl.  specialize (H6 b0). simpl in H6.
           destruct (b_eqb b0 (bid_of f)). lia. lia. 
         } 
       } 
     }
  }
}
Qed.


Lemma FOB_matchable (M: list fill_type)(B:list Bid)
(NZT:(forall m, In m M -> (tq m) > 0) )
(NDB:NoDup B) (Hanti: antisymmetric by_dbp):
Sorted by_dbp B -> 
Sorted m_dbp M -> 
All_matchable M -> 
(bids_of M) [<=] B ->
(forall b0, ttqb M b0 <= bq b0) -> 
All_matchable (FOB M B).
Proof. unfold FOB. intros. 
case B eqn:HB. rewrite FOB_aux_triv. auto. intros.
eapply FOB_aux_matchable_t with (t:=0)(b:=b)(B:=l).
all: auto. eauto. specialize (H3 b);lia. Qed.

(*####################################################################*)

(*Corrolary: Total traded quantity of FOB M B is same as M *)

(*####################################################################*)
Lemma FOB_size (M: list fill_type)(B: list Bid)(A:list Ask)
(NDA:NoDup A)(NDB:NoDup B) (NZT: forall m : fill_type, In m M -> tq m > 0): 
matching_in B A M ->  QM(M)=QM(FOB M B).
Proof. unfold FOB. intros. destruct H. destruct H.
destruct H0. destruct H1. 
rewrite <- QM_equal_QMa with (M:=M)(A:=A).
rewrite <- QM_equal_QMa with (M:=(FOB_aux M B 0))(A:=A).
eapply QMa_equal_QMa with (M1:= M) (M2:=(FOB_aux M B 0)).
intros. eapply FOB_aux_asks_invariant_t.
auto. cut (QM M <=  QB B). lia.
rewrite <- QM_equal_QMb with (B:=B).
eapply fill_size_vs_bid_size.
all:auto. intros. specialize (H1 b). 
assert((In b (bids_of M))\/~In b (bids_of M)). 
eauto. destruct H5. apply H1 in H5. auto.
apply ttqb_elim in H5. lia. 
assert((asks_of (FOB_aux M B 0)) [<=] (asks_of M)).
apply FOB_subA. eauto. Qed.

 




(*##########################################################################*)

(*Lemmas: Total traded quantity for each bids and asks in FOB is less than 
their limit quantity *)

(*#######################################################################*)
Lemma FOB_aux_ttqb_top_t (M: list fill_type)(B: list Bid)(A:list Ask)
(t:nat)(b:Bid)(NDB:NoDup (b::B)): 
ttqb (FOB_aux M (b::B) t) b <= bq b - t.
Proof. {
revert t. induction M as [ | m M'].
{ intro. simp FOB_aux. simpl;lia. }
{ intro. simp FOB_aux.
  destruct (Nat.eqb (tq m) (bq b - t)) eqn:Heq.
  { move /eqP in Heq. simpl. replace (b_eqb b b) with true.
    cut(ttqb (FOB_aux M' B 0) b = 0). lia.
    assert(~In b B). eauto. assert(bids_of ((FOB_aux M' B 0)) [<=] B).
    eapply FOB_aux_bids_subset. assert (~In b (bids_of (FOB_aux M' B 0))).
    eauto. eapply ttqb_elim in H1. exact. auto. 
  }
  { destruct (Nat.leb (tq m) (bq b - t)) eqn:Hle.
    {  simpl. replace (b_eqb b b) with true.
       move /leP in Hle.
       cut(ttqb (FOB_aux M' (b :: B) (t + tq m)) b <= bq b - (t+tq m)).
       lia. eapply IHM'. auto.
    }
    { simpl.
      replace (b_eqb b b) with true.
      cut(ttqb
      (FOB_aux
      ({|
       bid_of := bid_of m;
       ask_of := ask_of m;
       tq := tq m - (bq b - t);
       tp := tp m 
      |} :: M') B 0) b = 0). lia.
      assert(~In b B). eauto. 
      assert(bids_of ((FOB_aux
      ({|
       bid_of := bid_of m;
       ask_of := ask_of m;
       tq := tq m - (bq b - t);
       tp := tp m |} :: M') B 0)) [<=] B).
      eapply FOB_aux_bids_subset. assert (~In b (bids_of (FOB_aux
      ({|
       bid_of := bid_of m;
       ask_of := ask_of m;
       tq := tq m - (bq b - t);
       tp := tp m |} :: M') B 0))).
      eauto. eapply ttqb_elim in H1. exact. auto.
    }
   }
 } 
}Qed. 
  
 
Lemma FOB_aux_ttqb_top0 (M: list fill_type)(B: list Bid)
(A:list Ask)(b:Bid)(NDB:NoDup (b::B)): 
ttqb (FOB_aux M (b::B) 0) b <= bq b.
Proof. cut(ttqb (FOB_aux M (b :: B) 0) b <= bq b - 0). lia.
eapply FOB_aux_ttqb_top_t. eauto. exact. Qed.

Lemma FOB_aux_ttqb_t (M: list fill_type)(B: list Bid)(A:list Ask)(t:nat)(b b1:Bid)
(NDB:NoDup (b::B)): 
(b1=b -> ttqb (FOB_aux M (b::B) t) b1 <= bq b1 - t)/\
(b1<>b -> ttqb (FOB_aux M (b::B) t) b1 <= bq b1). 
Proof.
revert b1. funelim (FOB_aux M (b::B) t). 
{ split;intros;simp FOB_aux;simpl;lia. }
{ intros. destruct (b_eqb b1 b ) eqn: Hbb1. 
  { move /eqP in Hbb1. subst b1. split.
    intros. eapply FOB_aux_ttqb_top_t. auto. eauto.
    intros. elim H2. auto.   
  }
  { split;intros. 
    { subst b1. move /eqP in Hbb1. elim Hbb1. auto. }
    { rewrite<- Heqcall. 
      destruct (Nat.eqb (tq f) (bq b - t)) eqn:Hmb. (*EQ case when b1<>b *)
      { simpl. rewrite Hbb1. case l0 as [|b0 B'] eqn:Hl0. 
        rewrite FOB_aux_triv. simpl;lia.
        destruct (b_eqb b1 b0 ) eqn: Hb0b1.
        { move /eqP in Hb0b1. subst b0. 
          assert(ttqb (FOB_aux l (b1 :: B') 0) b1 <= bq b1 - 0). eapply H.
          all:try auto. eauto. lia. 
        }
        { eapply H. auto. auto. eauto. auto.
          auto. move /eqP in Hb0b1;auto.
        }
      }
      { destruct (Nat.leb (tq f) (bq b - t)) eqn: Hle.
           (*Less than case *) 
        { simpl. rewrite Hbb1.
          eapply H0. auto. auto. simpl. auto.
        }
        { case l0 as [|b0 B'] eqn:Hl0. 
          rewrite FOB_aux_triv. simpl. rewrite Hbb1. lia.
          destruct (b_eqb b1 b0 ) eqn: Hb0b1.
          {
          simpl. rewrite Hbb1.
          move /eqP in Hb0b1. subst b1. 
          assert(ttqb
          (FOB_aux
          ({|
             bid_of := bid_of f;
             ask_of := ask_of f;
             tq := tq f - (bq b - t);
             tp := tp f 
            |} :: l) (b0 :: B') 0) b0 <= bq b0 - 0). eapply H1.
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


Lemma FOB_ttqb (M: list fill_type)(B: list Bid)(A:list Ask)(b:Bid)(NDB:NoDup B): 
matching_in B A M-> (ttqb (FOB M B)) b <= bq b. 
Proof. unfold FOB. intros.
     destruct H. destruct H0. destruct H.
     destruct H2.
     case B as [| b0 B'] eqn: HB.
     rewrite FOB_aux_triv. simpl;lia.
     destruct (b_eqb b0 b) eqn: Hbb0.
     move /eqP in Hbb0.
     subst b0.
     eapply FOB_aux_ttqb_top0.
     eauto. eauto.
     eapply FOB_aux_ttqb_t.
     auto. eauto. move /eqP in Hbb0. auto. 
     Qed.

Lemma FOB_ttqa (M: list fill_type)(B: list Bid)(A:list Ask)(a:Ask)
(NDA:NoDup A)(NDB:NoDup B) (NZT:(forall m, In m M -> (tq m) > 0)): 
matching_in B A M -> (ttqa (FOB M B)) a <= sq a.
Proof.
     unfold FOB. intros.
     destruct H. destruct H0. destruct H.
     destruct H2.
     assert(ttqa M a = ttqa (FOB_aux M B 0) a).
     eapply FOB_asks_invariant with (M:=M)(B:=B)(a:=a).
     auto.
     rewrite <- QM_equal_QMb with (B:=B).
     eapply fill_size_vs_bid_size.
     all:auto. intros. specialize (H2 b). 
     assert((In b (bids_of M))\/~In b (bids_of M)). 
     eauto. destruct H5. apply H2 in H5. auto.
     apply ttqb_elim in H5. lia. 
     rewrite <- H4. specialize (H3 a). 
     assert((In a (asks_of M))\/~In a (asks_of M)). 
     eauto. destruct H5. apply H3 in H5. auto.
     apply ttqa_elim in H5. lia. Qed.
 

(*Lemma: FOB is matching*)
Lemma FOB_matching (M: list fill_type)(B: list Bid)(A:list Ask)
(NDA:NoDup A)(NDB:NoDup B) (NZT:(forall m, In m M -> (tq m) > 0))
(Hanti: antisymmetric by_dbp): 
Sorted by_dbp B ->
Sorted m_dbp M ->
matching_in B A M -> 
matching_in B A (FOB M B).
Proof. unfold matching_in. unfold matching.
       intros. split.
       { split.
         { apply FOB_matchable. all:auto.
           all: try apply H1.
           intros. assert((In b0 (bids_of M))\/~In b0 (bids_of M)).
           eauto. destruct H2. destruct H1. destruct H1. destruct H4.
           specialize (H4 b0). apply H4 in H2. auto.
           apply ttqb_elim in H2. lia. 
         }
         split.
         { intros. apply FOB_ttqb with (A:=A).
           eauto. eauto.
         }
         {
           intros. apply FOB_ttqa with (A:=A).
           eauto. eauto. auto. eauto.
         }
      }
      {
      split. apply FOB_subB. assert((asks_of (FOB M B)) [<=] (asks_of M)).
      eapply FOB_subA. destruct H1. destruct H1.  destruct H3.
      eauto. 
      }
Qed.
         
Theorem FOB_exists_and_correct (M: list fill_type)(B: list Bid)(A:list Ask)
(NDA:NoDup A)(NDB:NoDup B)(NZT:(forall m, In m M -> (tq m) > 0))
(Hanti: antisymmetric by_dbp): 
Sorted by_dbp B ->
Sorted m_dbp M ->
matching_in B A M ->
(exists M', (matching_in B A M')/\(fair_on_bids M' B)/\(QM(M) = QM(M'))).
Proof. exists (FOB M B).
split. 
     { apply FOB_matching. all:auto. }
split.
     { unfold fair_on_bids. intros.
       assert(Hb:In b (bids_of (FOB M B))). 
       eapply FOB_aux_more_competative_in.
       all:auto. eauto. apply H2. apply H2.
       exact.
       split.
       auto. eapply FOB_bids_fair. all:auto. eauto. auto.
     }
     eapply FOB_size.
     all:eauto.  
Qed.
End Fair.

Require Extraction.
Extraction  Language Scheme.
Recursive Extraction FOB.
Extraction  Language Haskell.
Recursive Extraction FOB.
Extraction  Language OCaml.
Recursive Extraction FOB.


