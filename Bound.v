Require Import ssreflect ssrbool.
Require Export Lists.List.
Require Export GenReflect SetSpecs.
Require Export DecList.
Require Export DecSort.
Require Export mBidAsk.
Require Export Quantity.
Require Export mMatching.
Require Export MatchingAlter.


Section Bound.


(*-------------- buyers_above and sellers_above relationship and results------------------*)



Definition buyers_above (p: nat)(B: list Bid): list Bid :=
  filter (fun x:Bid => Nat.leb p (bp x))  B.

Lemma buyers_above_elim (p:nat)(B: list Bid)(x:Bid):
  In x (buyers_above p B)-> bp(x) >= p.
Proof. { unfold buyers_above. intros H. 
         induction B. 
         {  simpl in H. destruct H. } 
         {  simpl in H.  
            destruct (Nat.leb p a) eqn: H1. 
            { simpl in H. destruct H. subst x. move /leP in H1. auto. 
            apply IHB in H. exact. }
            { apply IHB in H. exact. }}} Qed.
      
Lemma buyers_above_intro (p:nat)(B: list Bid)(x:Bid):
 ( In x B /\ (Nat.leb p x)) -> In x (buyers_above p B).
Proof. { intros H. destruct H as [H1  H2].  
         induction B. 
         { destruct H1. }
         { simpl in H1. 
           destruct H1 as [H1a | H1b].
           { subst x. simpl. destruct (Nat.leb p a) eqn: Hpa. auto.
            apply IHB. eapply insert_elim2. apply insert_intro3.
            auto. }
           { apply IHB in H1b. simpl. destruct (Nat.leb p a) eqn: Hpa.
             eauto. exact. }}} Qed.

Definition sellers_above (p: nat)(A: list Ask): list Ask :=
  filter (fun x:Ask => Nat.leb p (sp x)) (A).

Lemma sellers_above_elim (p:nat)(A: list Ask)(x:Ask):
  In x (sellers_above p A)-> sp(x) >= p.
Proof. { unfold sellers_above. intros H. 
         induction A. 
         {  simpl in H. destruct H. } 
         {  simpl in H.  
            destruct (Nat.leb p a) eqn: H1. 
            { simpl in H. destruct H. subst x. move /leP in H1. auto. 
            apply IHA in H. exact. }
            { apply IHA in H. exact. }}} Qed.
            
Lemma sellers_above_intro (p:nat)(A: list Ask)(x:Ask):
 ( In x A /\ Nat.leb p x ) -> In x (sellers_above p A).
Proof. { intros H. destruct H as [H1  H2].  
         induction A. 
         { destruct H1. }
         { simpl in H1. 
           destruct H1 as [H1a | H1b].
           { subst x. simpl. destruct (Nat.leb p a) eqn: Hpa. auto. 
             apply IHA. eapply insert_elim2. apply insert_intro3.
            auto. }
           { apply IHA in H1b. simpl. destruct (Nat.leb p a) eqn: Hpa.
             eauto. exact. }}} Qed.

Definition buyers_below (p: nat)(B: list Bid): list Bid :=
  filter (fun x:Bid => Nat.leb (bp x) p) (B).

Lemma buyers_below_intro (p:nat)(B: list Bid)(x:Bid):
 ( In x B /\ Nat.leb x p ) -> In x (buyers_below p B).
Proof. { intros H. destruct H as [H1  H2].  
         induction B. 
         { destruct H1. }
         { simpl in H1. 
           destruct H1 as [H1a | H1b].
           { subst x. simpl. destruct (Nat.leb a p) eqn: Hpa. auto. 
             apply IHB. eapply insert_elim2. apply insert_intro3.
            auto. }
           { apply IHB in H1b. simpl. destruct (Nat.leb a p) eqn: Hpa.
             eauto. exact. }}} Qed.

Lemma buyers_below_elim (p:nat)(B: list Bid)(x:Bid):
  In x (buyers_below p B)-> bp(x) <= p.
Proof.  { unfold sellers_above. intros H. 
         induction B. 
         {  simpl in H. destruct H. } 
         {  simpl in H.  
            destruct (Nat.leb a p) eqn: H1. 
            { simpl in H. destruct H. subst x. move /leP in H1. auto. 
            apply IHB in H. exact. }
            { apply IHB in H. exact. }}} Qed.

Definition sellers_below (p: nat)(A: list Ask): list Ask :=
  filter (fun x:Ask => Nat.leb (sp x) p) (A).

Lemma sellers_below_intro (p:nat)(A: list Ask)(x:Ask):
 ( In x A /\ Nat.leb x p ) -> In x (sellers_below p A).
Proof. { intros H. destruct H as [H1  H2].  
         induction A. 
         { destruct H1. }
         { simpl in H1. 
           destruct H1 as [H1a | H1b].
           { subst x. simpl. destruct (Nat.leb a p) eqn: Hpa. auto.
             apply IHA. eapply insert_elim2. apply insert_intro3.
            auto. }
           { apply IHA in H1b. simpl. destruct (Nat.leb a p) eqn: Hpa.
             eauto. exact. }}} Qed.

Lemma sellers_below_elim (p:nat)(A: list Ask)(x:Ask):
  In x (sellers_below p A)-> sp(x) <= p.
Proof. { unfold sellers_below. intros H. 
         induction A. 
         {  simpl in H. destruct H. } 
         {  simpl in H.  
            destruct (Nat.leb a p) eqn: H1. 
            { simpl in H. destruct H. subst x. move /leP in H1. auto. 
            apply IHA in H. exact. }
            { apply IHA in H. exact. }}} Qed.


(*#########Theorem in the paper###############*)

Lemma maching_buyer_right_plus_seller_left (B:list Bid)(A:list Ask):
forall p M, (matching_in B A M) -> 
QM(M) <= QB(buyers_above p (bids_of M)) + QA(sellers_below p (asks_of M)).
intros. induction M as [|m M']. simpl. auto.
simpl. assert(HM:matching_in B A (delete m (m::M'))).
       eauto. simpl in HM. replace (m_eqb m m) with true in HM.
       apply IHM' in HM.
       assert(tq m <= bq (bid_of m)).
       apply tqm_le_bqm with (M:=m::M')(B:=B)(A:=A).
       auto. auto.
       assert(tq m <= sq (ask_of m)).
       apply tqm_le_sqm with (M:=m::M')(B:=B)(A:=A).
       auto. auto.
       destruct (Nat.leb p (bid_of m)) eqn: Hpb;
       destruct (Nat.leb (ask_of m) p) eqn: Hpa.
       all:simpl. all: (try lia).
       { move /leP in Hpb. move /leP in Hpa.
         assert(ask_of m <= bid_of m).
         apply H. auto. lia.
       } eauto.
Qed.


End Bound.