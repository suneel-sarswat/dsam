
(* ------------   Work to be done : organise the hints properly ------------- *)



(* -------------------------------------------------------------------------------------

      This file contains all the important results about fair matching on bids.
      The main result is existance of a fair matching without compromizing its total quantity.

       by_dbp           <===>   order by decreasing bp or increasing time in case if bp is same
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

Require Export DecSort.
Require Export mBidAsk.
Require Export DecList.
Require Export mMatching.
Require Export Quantity.


(*Require Export AuctionInvar.*)

Section Fair_Bid.

Hypothesis unique_timestampbid:forall b1 b2, (btime b1 = btime b2) -> b1 = b2.

Definition by_dbp (b1:Bid) (b2:Bid) :=(Nat.ltb b2 b1) ||
((Nat.eqb b2 b1) && (Nat.leb (btime b1) (btime b2) )).
 
Definition fair_on_bids (M: list fill_type)(B: list Bid):=
  (forall b b', In b B /\ In b' B /\(b<>b') -> by_dbp b b'-> In b' (bids_of M) -> 
  (ttqb M b')>0-> 
  (In b (bids_of M)/\(ttqb M b= bq b))).

(*##################Sorting Criteria for Bids and Matchings for fair ####################*)
Lemma by_dbp_P : transitive by_dbp /\ DecSort.comparable by_dbp.
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
              right.
              move /eqP in H. move /eqP in H0. apply /andP.
              split. apply /eqP. lia. apply /leP. move /leP in H1. 
              move /leP in H2. lia. } }
            { unfold DecSort.comparable.
              unfold by_dbp. intros.  intros. destruct x. destruct y.  simpl. 
              assert((bp0 = bp)\/(bp0 < bp)\/(bp < bp0)). lia. destruct H.
              subst. assert(Nat.ltb bp bp = false). apply /ltP. lia. rewrite H. simpl.
              assert(Nat.eqb bp bp =true). auto. rewrite H0. simpl. 
              assert((btime0 <= btime)\/(btime < btime0)). lia. destruct H1.
              right. apply /leP. auto. left. apply /leP. lia.
              destruct H. left. apply /orP. left. apply /ltP. auto. right.
              apply /orP. left. apply /ltP. auto.
               } } Qed.

Lemma by_dbp_antisymmetric : antisymmetric by_dbp.
    Proof. unfold antisymmetric. intros. move /andP in H.
    destruct H as [H2 H3].
    unfold by_dbp in H2. unfold by_dbp in H3.
    move /orP in H2. move /orP in H3. 
    destruct H2;destruct H3. 
    move /ltP in H. move /ltP in H0. lia. 
    move /andP in H0. destruct H0. 
    move /ltP in H. move /eqP in H0. lia. 
    move /andP in H. destruct H. 
    move /ltP in H0. move /eqP in H.
    lia.
    move /andP in H. destruct H. 
    move /leP in H1.  
    move /andP in H0. destruct H0. 
    move /leP in H2. apply unique_timestampbid. lia.
Qed.


Lemma by_dbp_refl: reflexive by_dbp.
Proof. unfold reflexive. intros. unfold by_dbp. apply /orP. 
right. apply /andP. split. auto. apply nat_reflexive.  Qed.


Definition m_dbp (m1:fill_type) (m2:fill_type) := by_dbp (bid_of m1) (bid_of m2).

Lemma m_dbp_P : transitive m_dbp /\ DecSort.comparable m_dbp.
Proof. { split.
         { unfold transitive. unfold m_dbp. 
           intros. cut (transitive by_dbp). intros. eauto using by_dbp_P. 
            apply by_dbp_P. }
         { unfold DecSort.comparable. unfold m_dbp. intros.  eapply by_dbp_P. 
           } } Qed.
Lemma m_db_refl: reflexive m_dbp.
Proof. unfold reflexive. intros. unfold m_dbp. unfold by_dbp. 
apply /orP. right. apply /andP. split. auto. apply nat_reflexive.  Qed.

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
(*Hint Resolve by_dbp_refl m_dbp_refl : core.*)




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

Lemma FOB_aux_tp_subset (M: list fill_type) (B:list Bid) (t:nat):
trade_prices_of (FOB_aux M B t) [<=] trade_prices_of M.
Proof. apply FOB_aux_elim. all: auto.
{
 intros. destruct (Nat.eqb (tq f) (bq b -t0)) eqn: Hfb. 
 { simpl. cut (trade_prices_of (FOB_aux l l0 0) [<=] trade_prices_of l). 
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



(*This lemma (fob_asks_invariant) ensures that the total traded quantity for each ask in 
FOB is equal to it's  traded quantity in the input atching M. With this it is starightforward 
that the total traded quantity of an ask in FOB is less than or equal to it's  
ask quantity, since M is a matching. This lemma is also useful to ensures that the asks 
are not changed during fair on bids. This is useful to prove that during composition of FOB 
to FOA functions the fairness property of FOA remains invariant. This lemaa is also useful 
to show that the total traded quantity of FOB is same as input M. *)

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

(*In this lemma (fob_aux_top_bid_fair) we first show that the top bid in B is fully traded (trade 
quantity is total quantity. Note that, for arbitrary value of t, the statement is total quantity 
minus t. For t=0, the statement of following lemma is same as fully traded*)

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
by_dbp b1 b2 -> 
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
  subst b1;subst b2. auto. }
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
    assert(b=b1). apply by_dbp_antisymmetric. apply /andP.
    auto. subst. simpl. auto.
    (**)
    destruct H4. subst. move /eqP in Hbb1. destruct Hbb1. auto. exact.      
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
    

(*Following lemma (FOB_QM_ge_bqb) ensures that if a less competitive bid is part of FOB_aux then 
the total quantity traded in the matching should be more that or equal to more competitive bid*)

Lemma FOB_QM_ge_bqb (M: list fill_type)(B:list Bid)(b1 b2:Bid)(t:nat)
(NZT:(forall m, In m M -> (tq m) > 0) )(NDB:NoDup B)(Hnot: b1<>b2):
Sorted by_dbp B ->  by_dbp b1 b2 -> 
In b1 (bids_of (FOB_aux M B t)) -> In b2 (bids_of (FOB_aux M B t))
->  QM(M)>=bq b1 - t. 
Proof.  funelim (FOB_aux M B t). 
+ intros. simp FOB_aux in H1. simpl in H1;elim H1.
+ intros. simp FOB_aux in H1. simpl in H1;elim H1.
+ intros. rewrite <- Heqcall in H4. rewrite <- Heqcall in H5.
destruct (Nat.eqb (tq f) (bq b - t)) eqn:Heq0.  
{  (*Case : EQ *)
   simpl in H4. simpl in H5. move /eqP in Heq0. 
   destruct H4;destruct H5. 
   { subst. simpl. lia. }
   { subst. simpl. lia. }
   { (*this case contradict sorted. Move this into 
     a general result and automate. *)subst b2. assert (In b1 l0). eapply FOB_aux_bids_subset.
     eauto. assert(by_dbp b b1). 
     { eapply Sorted_elim4 with (a:=b)(x:=b1) in H2. auto. auto. }
       simpl. assert(b=b1). apply by_dbp_antisymmetric. apply /andP.
       auto. subst. lia. }
     { eapply H in H3. all: try (simpl;lia);auto. eauto. eauto. }  }
   (*End Case : EQ*)
{ 
   destruct (Nat.leb (tq f) (bq b - t)) eqn: Hle. 
   { (*Case : Top trade quantity is less than the the top bid  *)
     move /eqP in Heq0. move /leP in Hle. simpl in H4. simpl in H5.
     destruct H4;destruct H5. 
      { subst. destruct Hnot. auto. }
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
        eauto. eapply Sorted_elim4 with (a:=b)(x:=b1) in H2. 
          assert(b=b1). apply by_dbp_antisymmetric. apply /andP.
          auto. subst. destruct Hnot. auto.
          destruct H5. subst. destruct Hnot. auto.
          exact.
      }
      { eapply H0 with (b1:=b1) in H5. all: try (simpl;lia);auto. } 
   }
   { (*Case : Top trade quantity is more than the the top bid  *)
     move /eqP in Heq0. move /leP in Hle. simpl in H4. simpl in H5.
     destruct H4;destruct H5.
     { subst. destruct Hnot. auto. }
     { subst b. simpl. lia. }
     { subst b.  eapply Sorted_elim4 with (a:=b2)(x:=b1) in H2.
       assert(b2=b1). apply by_dbp_antisymmetric. apply /andP.
       auto. subst. destruct Hnot. auto.
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
(NZT:(forall m, In m M -> (tq m) > 0) )(NDB:NoDup (b::B))(Hnot: b1<>b2):
Sorted by_dbp (b::B) ->  
by_dbp b1 b2 -> 
In b1 (bids_of (FOB_aux M (b::B) t)) -> 
In b2 (bids_of (FOB_aux M (b::B) t)) ->  
(b1=b -> ttqb (FOB_aux M (b::B) t) b1 = bq b1 - t )/\
(b1<>b->ttqb (FOB_aux M (b::B) t) b1 = bq b1 ).
Proof.
funelim (FOB_aux M (b::B) t). auto. 
{ intros. destruct (b_eqb b1 b ) eqn: Hbb1. 
  { move /eqP in Hbb1. subst b. split.
    intros. eapply FOB_aux_top_bid_fair. auto. auto. 
    apply FOB_QM_ge_bqb with(b1:=b1) in H5. 
    all: try (simpl;lia);auto. }
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
          eapply Sorted_elim4 with (a:=b)(x:=b1)(lr:=by_dbp) in H2. 
          assert(b=b1). apply by_dbp_antisymmetric. apply /andP.
          auto. subst. destruct Hnot. auto.
          exact. }
         { case l0 as [| b0 B'] eqn:Hl0.
             { rewrite FOB_aux_triv in H4. simpl in H4. auto. }
             {  destruct (b_eqb b1 b0) eqn: Hbb0. 
                  { move /eqP in Hbb0. subst b0. eapply FOB_aux_top_bid_fair0.
                    auto. eauto. eapply FOB_QM_ge_bqb with (b1:=b1)(B:=(b1::B'))
                    (b2:=b2) in H5.
                    lia. auto. eauto. eauto. eauto. all:exact. }
                  { eapply H with (b:=b0)(b2:=b2). auto. eauto. eauto. eauto. eauto. eauto. 
                    exact. eauto. exact. move /eqP in Hbb0. exact. } 
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
            apply Sorted_elim4 with (a:=b)(x:=b1)(lr:=by_dbp) in H2. 
            assert(b=b1). apply by_dbp_antisymmetric. apply /andP.
            auto. subst.  destruct Hnot. auto.
            destruct H5. subst.  destruct Hnot. auto.
            exact. }
           { simpl. rewrite Hbb1. eapply H0 with (b2:=b2). 
             all: try auto.  } 
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
            apply Sorted_elim4 with (a:=b)(x:=b1) in H2. 
            assert(b=b1). apply by_dbp_antisymmetric. apply /andP.
            auto. subst.  destruct Hnot. auto.
            exact. }
          { case l0 as [| b0 B'].
            { rewrite FOB_aux_triv in H4. simpl in H4. auto. }
            { destruct (b_eqb b1 b0) eqn: Hbb0. 
              { move /eqP in Hbb0. subst b0. eapply FOB_aux_top_bid_fair0.
                simpl. intros. destruct H7. subst m. simpl. lia. auto. eauto. 
                simpl. eapply FOB_QM_ge_bqb with (b1:=b1)(B:=(b1::B'))(b2:=b2) in H4 . 
                simpl in H4. lia. intros. destruct H7. subst m. simpl. lia. eauto.
                eauto. auto. eauto. all:exact. 
              }
              { eapply H1 with (b1:=b0)(b2:=b1)(b3:=b2). 
                intros. destruct H7. subst m. simpl. lia. eauto.
                eauto. eauto. eauto. eauto. eauto. eauto. exact. exact. 
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
(NZT:(forall m, In m M -> (tq m) > 0) )(NDB:NoDup B)(Hnot: b1<>b2):
Sorted by_dbp B ->  
by_dbp b1 b2 -> 
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
(NZT:(forall m, In m M -> (tq m) > 0) )(NDB:NoDup B):
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
  assert(Hsort: Sorted by_dbp (b :: l0)). auto. 
   destruct (Nat.eqb (tq f) (bq b - t)) eqn: Heq. 
   { rewrite <- Heqcall in H8.
     simpl in H8. destruct H8. 
      { subst m. simpl. assert (In (bid_of f) (b::l0)). (*EQ: Base case *)
        apply H5. simpl. left. auto. assert (In f (f::l)). auto. 
        specialize (H4 f). apply H4 in H9. assert (bid_of f <= b).
        destruct (b_eqb b (bid_of f)) eqn:Hfb. move /eqP in Hfb. subst. auto.
        eapply Sorted_elim4 with (a:=b)(x:=bid_of f) in H2. (*EQ case*)
        unfold by_dbp in H2.
        move /orP in H2. destruct H2.
        { move /ltP in H2. lia. }
        { move /andP in H2. destruct H2. move /eqP in H2. lia. }
          move /eqP in Hfb. eapply included_elim2. eauto. lia. }
      { case l0 as [|b0 B'] eqn: HB. (*EQ: IH case*)
        { rewrite FOB_aux_triv in H8. inversion H8. } 
        { revert H8.
          eapply H. 
          { auto. } 
          { eauto. } 
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
               eapply m_dbp_and_by_dbp in H3. simpl in H3.
               eapply Sorted_elim4 with (a := (bid_of f))(x:=b) in H3.
               assert(b=(bid_of f)). apply by_dbp_antisymmetric. apply /andP.
               auto. subst. 
               eapply Sorted_elim4 with (a:=b)(x:=bid_of f) in H2. auto. 
               eapply included_elim2. eauto.
               eauto. 
               exact. }
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
          specialize (H4 f). apply H4 in H9. 
           destruct (b_eqb b (bid_of f)) eqn:Hfb. move /eqP in Hfb. subst. auto.
          eapply Sorted_elim4 with (a:=b)(x:=bid_of f) in H2. unfold by_dbp in H2.
          move /orP in H2. destruct H2.
          { move /ltP in H2. lia. }
          { move /andP in H2. destruct H2. move /eqP in H2. lia. }
          move /eqP in Hfb. eapply included_elim2. eauto. }
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
            { simpl in H5. eapply Sorted_elim4 with (a:=b)(x:=bid_of f) in H2.
              eapply m_dbp_and_by_dbp in H3. simpl in H3.
               eapply Sorted_elim4 with (a := (bid_of f))(x:=b) in H3.
               assert(b=(bid_of f)).  apply by_dbp_antisymmetric. apply /andP.
               auto. subst b. destruct Hbm. auto.
               exact. eapply included_elim2. eauto. }
            { eapply  ttqb_elim in H9. lia. } 
          } 
        }
      }
      { simpl in H8. destruct H8.  
      (*GT case*) 
        { subst m. simpl. assert (In (bid_of f) (b::l0)). (*GT: Base case*)
          apply H5. simpl. left. auto. assert (In f (f::l)). auto. 
          specialize (H4 f). apply H4 in H9.
          destruct (b_eqb b (bid_of f)) eqn:Hfb. move /eqP in Hfb. subst. auto.
          eapply Sorted_elim4 with (a:=b)(x:=bid_of f) in H2.
          unfold by_dbp in H2.
          move /orP in H2. destruct H2.
          { move /ltP in H2. lia. }
          { move /andP in H2. destruct H2. move /eqP in H2. lia. } move /eqP in Hfb.
             eapply included_elim2. eauto.
        }
        { case l0 as [|b0 B'] eqn: HB.  (*GT: IH case*)
          { rewrite FOB_aux_triv in H8. inversion H8. }
          { eapply H1 in H8. 
            all: try auto. simpl. intros. destruct H9. subst m0.
            simpl. move /leP in Hle. lia. auto. eauto. eauto. 
            eapply m_dbp_and_by_dbp in H3 as Hm3. simpl in Hm3.
            revert Hm3. constructor. eauto. intros. 
            unfold m_dbp. simpl. apply Sorted_elim4 with (x0:=(bid_of x)) in Hm3.
            exact. eauto.  
            unfold All_matchable. simpl. intros.
            destruct H9. subst m0. simpl. eauto. eauto. simpl. 
            move /leP in Hle. simpl in H7. 
            destruct (b_eqb b (bid_of f)) eqn: Hbm.
            move /eqP in Heq. lia. move /eqP in Hbm. 
            assert (In b (bids_of l) \/ ~In b (bids_of l)). eauto.
            destruct H9. 
            { simpl in H5. eapply Sorted_elim4 with (a:=b)(x:=bid_of f) in H2. 
              eapply m_dbp_and_by_dbp in H3. simpl in H3.
               eapply Sorted_elim4 with (a := (bid_of f))(x:=b) in H3.
               assert(b=(bid_of f)). apply by_dbp_antisymmetric. apply /andP.
               auto. subst. destruct Hbm. auto.
               exact.  eapply included_elim2. eauto. }
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
(NDB:NoDup B):
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



(*################################################################################*)

(*Lemmas: IR in FOB *)

(*################################################################################*)

Lemma FOB_aux_IR (M: list fill_type)(B:list Bid)(b:Bid)(t:nat)
(NZT:(forall m, In m M -> (tq m) > 0) )(NDB:NoDup B):
Sorted by_dbp (b::B) -> 
Sorted m_dbp M -> 
Is_IR M -> 
(bids_of M) [<=] (b::B) ->
(forall b0, ttqb M b0 <= bq b0) -> 
(ttqb M b <= bq b - t) ->  
Is_IR (FOB_aux M (b::B) t).

Proof. { funelim ((FOB_aux M (b::B) t)).
+ intros. simp FOB_aux. 
+ unfold Is_IR. intros. 
destruct (Nat.eqb (tq f) (bq b - t)) eqn: Heq. (*EQ case*)
   { rewrite <- Heqcall in H8.
     simpl in H8. destruct H8.  
      { subst m. unfold rational.
        simpl. assert (In (bid_of f) (b::l0)). (*EQ: Base case *)
        apply H5. simpl. left. auto. assert (In f (f::l)). auto. 
        specialize (H4 f). apply H4 in H9. assert (bid_of f <= b).  
        destruct (b_eqb b (bid_of f)) eqn:Hfb. move /eqP in Hfb. subst. auto.
        eapply Sorted_elim4 with (a:=b)(x:=bid_of f) in H2. unfold by_dbp in H2.
        move /orP in H2. destruct H2.
        { move /ltP in H2. lia. }
        { move /andP in H2. destruct H2. move /eqP in H2. lia. }
        auto. move /eqP in Hfb. eapply included_elim2. eauto. unfold rational in H9. lia. }
      { case l0 as [|b0 B'] eqn: HB. (*EQ: IH case*)
        { rewrite FOB_aux_triv in H8. inversion H8. } 
        { revert H8.
          eapply H. 
          { auto. } 
          { eauto. } 
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
               eapply Sorted_elim4 with (a:=b)(x:=bid_of f) in H2. 
              eapply m_dbp_and_by_dbp in H3. simpl in H3.
               eapply Sorted_elim4 with (a := (bid_of f))(x:=b) in H3.
               assert(b=(bid_of f)). apply by_dbp_antisymmetric. apply /andP.
               auto. subst. destruct Hbm. auto.
               exact.  eapply included_elim2. eauto.
             }
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
          destruct (b_eqb b (bid_of f)) eqn:Hfb. move /eqP in Hfb. subst. auto.
          eapply Sorted_elim4 with (a:=b)(x:=bid_of f) in H2. unfold by_dbp in H2.
          move /orP in H2. destruct H2.  
          { move /ltP in H2. lia. }
          { move /andP in H2. destruct H2. move /eqP in H2. lia. } 
            move /eqP in Hfb. eapply included_elim2. eauto. unfold rational in H9. unfold rational. simpl. lia. 
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
              eapply Sorted_elim4 with (a:=b)(x:=bid_of f) in H2. 
              eapply m_dbp_and_by_dbp in H3. simpl in H3.
               eapply Sorted_elim4 with (a := (bid_of f))(x:=b) in H3.
               assert(b=(bid_of f)). apply by_dbp_antisymmetric. apply /andP.
               auto. subst. destruct Hbm. auto.
               exact. eapply included_elim2. eauto.
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
          destruct (b_eqb b (bid_of f)) eqn:Hfb. move /eqP in Hfb. subst. auto.
          eapply Sorted_elim4 with (a:=b)(x:=bid_of f) in H2. unfold by_dbp in H2.
          move /orP in H2. destruct H2. 
          { move /ltP in H2. lia. }
          { move /andP in H2. destruct H2. move /eqP in H2. lia. }
            move /eqP in Hfb. eapply included_elim2. eauto. unfold rational in H9. unfold rational. simpl. lia. 
        }
        { case l0 as [|b0 B'] eqn: HB.  (*GT: IH case*)
          { rewrite FOB_aux_triv in H8. inversion H8. }
          { eapply H1 in H8. 
            all: try auto.
            { simpl. intros. destruct H9. subst m0.
            simpl. move /leP in Hle. lia. auto. }
            { eauto. }
            { eauto. } 
            { eapply m_dbp_and_by_dbp in H3 as Hm3. simpl in Hm3.
            revert Hm3. constructor. eauto. intros. 
            unfold m_dbp. simpl. apply Sorted_elim4 with (x0:=(bid_of x)) in Hm3.
            exact. eauto. } 
            { unfold Is_IR. simpl. intros.
            destruct H9. 
              { subst m0. simpl. unfold rational. 
              eauto. eauto. simpl. apply H4. auto. }  
              { apply H4. eauto. }
            }
            { simpl. move /leP in Hle. simpl in H7. 
            destruct (b_eqb b (bid_of f)) eqn: Hbm.
            move /eqP in Heq. lia. move /eqP in Hbm. 
            assert (In b (bids_of l) \/ ~In b (bids_of l)). eauto.
            destruct H9. 
            { simpl in H5. 
              eapply Sorted_elim4 with (a:=b)(x:=bid_of f) in H2. 
              eapply m_dbp_and_by_dbp in H3. simpl in H3.
               eapply Sorted_elim4 with (a := (bid_of f))(x:=b) in H3.
               assert(b=(bid_of f)). apply by_dbp_antisymmetric. apply /andP.
               auto. subst. destruct Hbm. auto.
               exact. eapply included_elim2. eauto.
            }
            { simpl in H5.
              eapply Subset_elim0 with (a1:=(bid_of f))(a2:=b)
              (l2:=(b0::B')) in H5. auto. auto. auto. 
            } 
           }
           { simpl. intros. simpl in H6. specialize (H6 b1). 
             destruct (b_eqb b1 (bid_of f)).
           lia. exact H6. 
           }
           { simpl.  specialize (H6 b0). simpl in H6.
           destruct (b_eqb b0 (bid_of f)). lia. lia. 
         } 
       } 
     }
  }
} }
Qed.


Lemma FOB_IR (M: list fill_type)(B:list Bid)
(NZT:(forall m, In m M -> (tq m) > 0) )
(NDB:NoDup B) :
Sorted by_dbp B -> 
Sorted m_dbp M -> 
Is_IR M -> 
(bids_of M) [<=] B ->
(forall b0, ttqb M b0 <= bq b0) -> 
Is_IR (FOB M B).
Proof. unfold FOB. intros. 
case B eqn:HB. rewrite FOB_aux_triv. 
unfold Is_IR. intros. elim H4. unfold Is_IR. intros.
eapply FOB_aux_IR with (t:=0)(b:=b)(B:=l) in H4.
all: auto. eauto. specialize (H3 b);lia. Qed.



(*####################################################################*)

(*Uniform FOA*)

(*####################################################################*)

Lemma FOB_uniform (M:list fill_type)(B: list Bid):
Uniform M -> Uniform (FOB M B).
Proof. unfold Uniform. intros.
assert(trade_prices_of (FOB M B) [<=] trade_prices_of M).
apply FOB_aux_tp_subset. eauto. Qed.






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

 

(*####################Used in compositions #########################*)

Lemma FOB_asks_M_subset_asks_FOB (M: list fill_type)(B:list Bid)(NDB:NoDup B)
(NZT: forall m : fill_type, In m M -> tq m > 0): 
(forall b : Bid, In b (bids_of M) -> ttqb M b <= bq b) ->
bids_of M [<=]B ->
asks_of M [<=] asks_of (FOB M B).
Proof. 
unfold FOB. intros. 
assert(QB B>=QM M).
rewrite <- QM_equal_QMb with (B:=B).
eapply fill_size_vs_bid_size.
all:auto. intros. eauto.
apply ttqa_equal_implies_subet. auto.
intros.
apply FOB_asks_invariant with (M:=M)(B:=B). auto. lia.
Qed.



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
     
(******************FOB_NZT*************************)

Lemma FOB_aux_NZT (M: list fill_type)(B:list Bid)(t:nat)(b:Bid)
(NZT:(forall m, In m M -> (tq m) > 0))(NDB:NoDup (b::B))
(NZB:(forall b0, In b0 (b::B) -> (bq b0) > 0))
:
(bq b) > t-> (forall m, In m (FOB_aux M (b::B) t) -> (tq m) > 0).
Proof. { funelim ((FOB_aux M (b::B) t)).
+ intros. simp FOB_aux in H0. 
+ intros. rewrite <- Heqcall in H3. 
destruct (Nat.eqb (tq f) (bq b - t)) eqn: Heq.
{ simpl in H3. destruct H3. subst m. simpl. lia.
  case l0 as [|b0 B'] eqn:Hl0. rewrite FOB_aux_triv in H3. 
  elim H3. apply H in H3. all:auto. eauto.
}
{ destruct (Nat.leb (tq f) (bq b - t)) eqn: Hle.
  { simpl in H3. destruct H3. subst m. simpl. apply NZT.
    auto. apply H0 in H3. all:auto. move /leP in Hle.
    move /eqP in Heq.
    lia.
  }
{ simpl in H3. destruct H3. subst m. simpl. lia.
  case l0 as [|b0 B'] eqn:Hl0. rewrite FOB_aux_triv in H3. 
  elim H3. apply H1 in H3. all:auto.
  intros. simpl in H4. destruct H4. 
  subst m0. simpl. move /leP in Hle.
    move /eqP in Heq.
    lia. eauto. eauto.
} } } Qed.

Lemma FOB_NZT (M: list fill_type)(B:list Bid)
(NZT:(forall m, In m M -> (tq m) > 0))(NDB:NoDup B)
(NZB:(forall b0, In b0 B -> (bq b0) > 0))
:
(forall m, In m (FOB M B) -> (tq m) > 0).
Proof. unfold FOB. induction B. rewrite FOB_aux_triv.
       simpl. intros. elim H.
       apply FOB_aux_NZT. auto. eauto. eauto. auto. Qed.

(*#############END:NZT FOB######################*)


Lemma ttqb_incl (M M': list fill_type) (b:Bid):
included M M'  -> ttqb M b <= ttqb M' b.
Proof. revert M. induction M' as [ |m M0]. intros. 
       assert(M = nil). eauto. subst. simpl. lia.
       intros. 
       destruct (b_eqb b (bid_of m)) eqn: Hbm.
       {
       replace (m_eqb m m) with true. simpl. rewrite Hbm.
       replace (m_eqb m m) with true. 
       assert(In m M\/~In m M). eauto.
       destruct H0. apply ttqb_delete_m_ofb with (b:=b) in H0.
       rewrite H0. cut(ttqb (delete m M) b <=ttqb M0 b).
       lia. eapply IHM0. 
       assert(included (delete m M) M0). 
       eapply included_elim3a with (a:=m) in H.
       simpl in H. replace (m_eqb m m) with true in H. auto.
       eauto.
       auto. move /eqP in Hbm. auto. 
       assert(included M M0). 
       eapply included_elim3b in H. auto. auto.
       apply IHM0 in H1. lia. eauto. eauto. }
       { simpl. rewrite Hbm.
       replace (m_eqb m m) with true. 
       assert(In m M\/~In m M). eauto.
       destruct H0. apply ttqb_delete_m_not_ofb with (b:=b) in H0.
       rewrite H0.
       eapply IHM0. 
       assert(included (delete m M) M0). 
        eapply included_elim3a with (a:=m) in H.
       simpl in H. replace (m_eqb m m) with true in H. auto.
       eauto.
       auto. move /eqP in Hbm. auto. 
       assert(included M M0).  eapply included_elim3b in H. auto. auto.
       apply IHM0 in H1. lia. eauto.
} Qed.
Lemma ttqb_inv (M M': list fill_type) (b:Bid):
perm M M'  -> ttqb M b = ttqb M' b.
Proof. intros. unfold perm in H. move /andP in H.
destruct H. apply ttqb_incl with (b:=b) in H.
apply ttqb_incl with (b:=b) in H0. lia. Qed.
     
Lemma ttqa_incl (M M': list fill_type) (a:Ask):
included M M'  -> ttqa M a <= ttqa M' a.
Proof. revert M. induction M' as [ |m M0]. intros. 
       assert(M = nil). eauto. subst. simpl. lia.
       intros. 
       destruct (a_eqb a (ask_of m)) eqn: Hbm.
       {
       replace (m_eqb m m) with true. simpl. rewrite Hbm.
       replace (m_eqb m m) with true. 
       assert(In m M\/~In m M). eauto.
       destruct H0. apply ttqa_delete_m_ofa with (a:=a) in H0.
       rewrite H0. cut(ttqa (delete m M) a <=ttqa M0 a).
       lia. eapply IHM0. 
       assert(included (delete m M) M0). 
       eapply included_elim3a with (a0:=m) in H.
       simpl in H. replace (m_eqb m m) with true in H. auto.
       eauto.
       auto. move /eqP in Hbm. auto. 
       assert(included M M0).
        eapply included_elim3b in H. auto. auto.
       apply IHM0 in H1. lia. eauto. eauto. }
       { simpl. rewrite Hbm.
       replace (m_eqb m m) with true. 
       assert(In m M\/~In m M). eauto.
       destruct H0. apply ttqa_delete_m_not_ofa with (a:=a) in H0.
       rewrite H0.
       eapply IHM0. 
       assert(included (delete m M) M0). 
       eapply included_elim3a with (a0:=m) in H.
       simpl in H. replace (m_eqb m m) with true in H. auto.
       eauto.       auto. move /eqP in Hbm. auto. 
       assert(included M M0).
        eapply included_elim3b in H. auto. auto.
       apply IHM0 in H1. lia. eauto.
} Qed.

Lemma ttqa_inv (M M': list fill_type) (a:Ask):
perm M M'  -> ttqa M a = ttqa M' a.
Proof. intros. unfold perm in H. move /andP in H.
destruct H. apply ttqa_incl with (a:=a) in H.
apply ttqa_incl with (a:=a) in H0. lia. Qed.



Lemma match_inv (M M': list fill_type) (B B': list Bid) (A A' : list Ask):
perm M  M' -> perm B B' -> perm A A' -> matching_in B A M -> matching_in B' A' M'.
Proof. { intros. destruct H2. destruct H3. destruct H2. destruct H5.
 unfold matching_in. unfold matching.
 assert(perm (bids_of M') (bids_of M)).
 { eapply bids_of_perm in H. auto. }
 assert(perm (asks_of M') (asks_of M)).
 {  eapply asks_of_perm in H. auto. }
 split. { split. {
 unfold All_matchable. unfold All_matchable in H2. 
 unfold perm in H. move /andP in H. destruct H. eapply included_elim5 in H9.
 eauto. } split. 
  {intros. eapply ttqb_inv with (b:=b) in H as Ha. rewrite <- Ha.
   assert(In b (bids_of M)\/~In b (bids_of M)). eauto.
   destruct H10. apply H5. auto. apply ttqb_elim in H10. lia. }
  {intros. eapply ttqa_inv with (a:=a) in H as Ha. rewrite <- Ha.
   assert(In a (asks_of M)\/~In a (asks_of M)). eauto.
   destruct H10. apply H6. auto. apply ttqa_elim in H10. lia. } }
   split. assert(B [<=] B'). eapply perm_subset in H0. eauto. eauto. eauto.
   eauto. assert(A [<=] A'). eapply perm_subset in H1. eauto. eauto. eauto. eauto.
   } Qed.
 
 
(*Lemma: FOB is matching*)
Lemma FOB_matching (M: list fill_type)(B: list Bid)(A:list Ask)
(NDA:NoDup A)(NDB:NoDup B) (NZT:(forall m, In m M -> (tq m) > 0)): 
matching_in B A M -> 
matching_in B A (FOB (sort m_dbp M) (sort by_dbp B)).
Proof. unfold matching_in. unfold matching.
       intros. assert(bids_of M [<=] B /\ asks_of M [<=] A).
           apply H. destruct H0. 
           
           split.
       { split.
         { apply FOB_matchable. intros. 
           assert(In m M). eapply sort_elim. eauto. auto. eauto.
           auto. eapply sort_correct. apply by_dbp_P.
           apply by_dbp_P. eapply sort_correct. apply m_dbp_P.
           apply m_dbp_P. eauto. eauto. intros. 
           assert(ttqb (sort m_dbp M) b0 = ttqb M b0).
           eapply ttqb_inv. eauto. rewrite H2.
           assert(In b0 (bids_of M)\/~In b0 (bids_of M)). eauto.
           destruct H3. apply H. auto. apply ttqb_elim in H3. lia.
         }
         split.
         {
          intros. apply FOB_ttqb with (A:=A).
           eauto. assert(perm M (sort m_dbp M) ). eauto.
           assert(perm B (sort by_dbp B)). eauto.
           eapply match_inv with (B':=(sort by_dbp B)) (M':=(sort m_dbp M))(A':=A) in H3.
           auto. eauto. eauto. apply H.
         }
         {
          intros. apply FOB_ttqa with (A:=A).
           eauto. eauto. intros. assert(In m M). eapply sort_elim. eauto. auto. 
           assert(perm M (sort m_dbp M) ). eauto.
           assert(perm B (sort by_dbp B)). eauto.
           eapply match_inv with (B':=(sort by_dbp B)) (M':=(sort m_dbp M))(A':=A) in H3.
           auto. eauto. eauto. apply H.
         } }
      {
      split. assert(bids_of (FOB (sort m_dbp M) (sort by_dbp B))[<=](sort by_dbp B)). 
      eapply FOB_subB. eauto.
      assert(asks_of (FOB (sort m_dbp M) (sort by_dbp B))[<=](asks_of (sort m_dbp M))).
      eapply FOB_subA. eauto. 
      }
Qed.
         
Theorem FOB_exists_and_correct (M: list fill_type)(B: list Bid)(A:list Ask)
(NDA:NoDup A)(NDB:NoDup B)(NZT:(forall m, In m M -> (tq m) > 0)): 
matching_in B A M ->
(exists M', (matching_in B A M')/\(fair_on_bids M' B)/\(QM(M) = QM(M'))).
Proof. exists (FOB (sort m_dbp M) (sort by_dbp B)).
split. 
     { apply FOB_matching. all:auto. }
split. 
     { unfold fair_on_bids. intros.
       assert(Hb:In b (bids_of (FOB (sort m_dbp M) (sort by_dbp B)))). 
       eapply FOB_aux_more_competative_in.
       all:auto. eauto.  eapply sort_correct. apply by_dbp_P.
       apply by_dbp_P. eauto. destruct H0. eapply sort_intro in H0.  eauto.
       destruct H0. destruct H4. eapply sort_intro in H4.  eauto.
       eauto. 
       split.
       auto. eapply FOB_bids_fair with (b1:=b)(b2:=b'). all:auto. intros. assert(In m M). 
       eauto.  auto. apply H0.
       eapply sort_correct. apply by_dbp_P.
       apply by_dbp_P. 
     }
     assert(QM(sort m_dbp M) = QM(M)). eauto. rewrite <- H0. eapply FOB_size.
     all:eauto. eapply match_inv with (B':=(sort by_dbp B))(M':=(sort m_dbp M)) in H.
     eauto. eauto. eauto. auto.
Qed.



End Fair_Bid.

