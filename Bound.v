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
  filter (fun x:Bid => Nat.ltb (bp x) p) (B).

Lemma buyers_below_intro (p:nat)(B: list Bid)(x:Bid):
 ( In x B /\ Nat.ltb x p ) -> In x (buyers_below p B).
Proof. { intros H. destruct H as [H1  H2].  
         induction B. 
         { destruct H1. }
         { simpl in H1. 
           destruct H1 as [H1a | H1b].
           { subst x. simpl. destruct (Nat.ltb a p) eqn: Hpa. auto. 
             apply IHB. eapply insert_elim2. apply insert_intro3.
            auto. }
           { apply IHB in H1b. simpl. destruct (Nat.ltb a p) eqn: Hpa.
             eauto. exact. }}} Qed.

Lemma buyers_below_elim (p:nat)(B: list Bid)(x:Bid):
  In x (buyers_below p B)-> bp(x) < p.
Proof.  { unfold sellers_above. intros H. 
         induction B. 
         {  simpl in H. destruct H. } 
         {  simpl in H.  
            destruct (Nat.ltb a p) eqn: H1. 
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

(*Now we prove our main combinatorial result *) 



Lemma buyers_above_nodup (B:list Bid) (Ndb: NoDup B) (p:nat):
NoDup (buyers_above p B).
Proof. induction B. simpl. constructor. simpl. 
destruct (Nat.leb p a) eqn: Hpa. assert (H0:~In a B).
eauto. assert (H1:~In a (buyers_above p B)). eauto. 
assert (H2: NoDup B). eauto. eapply IHB in H2. eauto.
assert (H2: NoDup B). eauto. eapply IHB in H2. eauto. Qed.

Lemma sellers_below_nodup (A:list Ask) (Nda: NoDup A) (p:nat):
NoDup (sellers_below p A).
Proof. induction A. simpl. constructor. simpl. 
destruct (Nat.leb a p) eqn: Hpa. assert (H0:~In a A).
eauto. assert (H1:~In a (sellers_below p A)). eauto. 
assert (H2: NoDup A). eauto. eapply IHA in H2. eauto.
assert (H2: NoDup A). eauto. eapply IHA in H2. eauto. Qed.


Definition Mbgep (p: nat)(M: list fill_type): list fill_type :=
  filter (fun x:fill_type => Nat.leb p (bp (bid_of x))) M.

Definition Mbltp (p: nat)(M: list fill_type): list fill_type :=
  filter (fun x:fill_type => Nat.ltb (bp (bid_of x)) p) M.


Lemma Mbgep_elim (p:nat)(M: list fill_type)(x:fill_type):
  In x (Mbgep p M)-> (bp (bid_of x)) >= p.
Proof. { unfold Mbgep. intros H. 
         induction M. 
         {  simpl in H. destruct H. } 
         {  simpl in H.  
            destruct (Nat.leb p (bid_of a)) eqn: H1. 
            { simpl in H. destruct H. subst x. move /leP in H1. auto. 
            apply IHM in H. exact. }
            { apply IHM in H. exact. }}} Qed.
      
Lemma Mbgep_intro (p:nat)(M: list fill_type)(x:fill_type):
 ( In x M /\ (Nat.leb p (bid_of x))) -> In x (Mbgep p M).
Proof. { intros H. destruct H as [H1  H2].  
         induction M. 
         { destruct H1. }
         { simpl in H1. 
           destruct H1 as [H1a | H1b].
           { subst x. simpl. destruct (Nat.leb p (bid_of a)) eqn: Hpa. auto.
             elim H2.
            apply IHM. eapply insert_elim2. apply insert_intro3.
            auto. }
           { apply IHM in H1b. simpl. destruct (Nat.leb p (bid_of a)) eqn: Hpa.
             eauto. exact. }}} Qed.

Lemma Mbltp_elim (p:nat)(M: list fill_type)(x:fill_type):
  In x (Mbltp p M)->  p> (bp (bid_of x)).
Proof. { unfold Mbltp. intros H. 
         induction M. 
         {  simpl in H. destruct H. } 
         {  simpl in H.  
            destruct (Nat.ltb (bid_of a) p) eqn: H1. 
            { simpl in H. destruct H. subst x. move /leP in H1. auto. 
            apply IHM in H. exact. }
            { apply IHM in H. exact. }}} Qed.


      
Lemma Mbltp_intro (p:nat)(M: list fill_type)(x:fill_type):
 ( In x M /\ (Nat.ltb (bid_of x) p)) -> In x (Mbltp p M).
Proof. { intros H. destruct H as [H1  H2].  
         induction M. 
         { destruct H1. }
         { simpl in H1. 
           destruct H1 as [H1a | H1b].
           { subst x. simpl. destruct (Nat.ltb (bid_of a) p) eqn: Hpa. auto.
             elim H2.
            apply IHM. eapply insert_elim2. apply insert_intro3.
            auto. }
           { apply IHM in H1b. simpl. destruct (Nat.ltb (bid_of a) p) eqn: Hpa.
             eauto. exact. }}} Qed.


Lemma Mbgep_bids_subsetBp (p:nat)(M: list fill_type)(B:list Bid):
bids_of M [<=] B -> bids_of ((Mbgep p M)) [<=] (buyers_above p B).
Proof. intros. unfold "[<=]". intros. 
set (M1:=(Mbgep p M)). assert(exists x, In x M1/\a=bid_of x).
eauto. destruct H1 as [m H1]. destruct H1. apply Mbgep_elim in H1 as H3.
assert(In m M). eauto. assert(In (bid_of m) B). eauto. 
assert(In a (buyers_above p B)). apply buyers_above_intro.
subst. split. auto. apply /leP. lia. auto. Qed.

Lemma Mbgep_ttqb (p:nat)(M: list fill_type)(b:Bid):
ttqb ((Mbgep p M)) b <= ttqb M b.
Proof. induction M as [| m M']. simpl. auto.
simpl. 
destruct (Nat.leb p (bid_of m)) eqn: Hpm;destruct (b_eqb b (bid_of m)) eqn:Hbm.
{ simpl. rewrite Hbm. lia. }
{ simpl. rewrite Hbm. lia. }
{ lia. }
{ lia. } Qed.


Lemma Mbltp_asks_subsetAp (p:nat)(M: list fill_type)(A:list Ask):
All_matchable M -> asks_of M [<=] A -> asks_of ((Mbltp p M)) [<=] (sellers_below p A).
Proof.
intros. unfold "[<=]". intros. 
set (M1:=(Mbltp p M)). assert(exists x, In x M1/\a=ask_of x).
eauto. destruct H2 as [m H2]. destruct H2. apply Mbltp_elim in H2 as H4.
assert(In m M). eauto. assert(In (ask_of m) A). eauto. 
assert(In a (sellers_below p A)). apply sellers_below_intro.
subst. split. auto. apply /leP. 
apply H in H5.
 lia. auto. Qed.

Lemma Mbltp_ttqa (p:nat)(M: list fill_type)(a:Ask):
ttqa ((Mbltp p M)) a <= ttqa M a.
Proof. induction M as [| m M']. simpl. auto.
simpl. 
destruct (Nat.ltb (bid_of m) p) eqn: Hpm;destruct (a_eqb a (ask_of m)) eqn:Ham.
{ simpl. rewrite Ham. lia. }
{ simpl. rewrite Ham. lia. }
{ lia. }
{ lia. } Qed.



Lemma Mbgep_bound (p:nat)(M: list fill_type)(B:list Bid)(A:list Ask)
(NDB:NoDup B):
matching_in B A M -> QM((Mbgep p M)) <= QB(buyers_above p B).
Proof.
intros. rewrite <- QM_equal_QMb with (B:=(buyers_above p B)).
apply fill_size_vs_bid_size. apply buyers_above_nodup.
auto. intros.
assert(bids_of ((Mbgep p M)) [<=] (buyers_above p B)).
apply Mbgep_bids_subsetBp. apply H.
assert(ttqb (Mbgep p M) b <= ttqb M b).
apply Mbgep_ttqb. cut(ttqb M b <= bq b).
lia.
assert(In b (bids_of M)\/~In b (bids_of M)).
eauto. destruct H3.
apply H. auto. apply ttqb_elim in H3. lia.
apply buyers_above_nodup. auto. apply Mbgep_bids_subsetBp. apply H. 
Qed.

Lemma Mbltp_bound (p:nat)(M: list fill_type)(B:list Bid)(A:list Ask)
(NDA:NoDup A):
matching_in B A M -> QM((Mbltp p M)) <= QA(sellers_below p A).
Proof.
intros. rewrite <- QM_equal_QMa with (A:=(sellers_below p A)).
apply fill_size_vs_ask_size. apply sellers_below_nodup. auto. intros.
assert(asks_of ((Mbltp p M)) [<=] (sellers_below p A)).
apply Mbltp_asks_subsetAp. apply H. apply H. 
assert(ttqa (Mbltp p M) a <= ttqa M a).
apply Mbltp_ttqa. cut(ttqa M a <= sq a).
lia.
assert(In a (asks_of M)\/~In a (asks_of M)).
eauto. destruct H3.
apply H. auto. apply ttqa_elim in H3. lia.
apply sellers_below_nodup. auto. apply Mbltp_asks_subsetAp. apply H. apply H.
Qed.


Lemma M_bound_volume (p:nat)(M: list fill_type):
QM(M) = QM(Mbgep p M) + QM(Mbltp p M).
Proof. induction M. simpl. auto.
simpl. 
destruct (Nat.leb p (bid_of a)) eqn:H1;destruct(Nat.ltb (bid_of a) p) eqn:H2.
{ move /leP in H1. move /leP in H2. lia. }
{ move /leP in H1. move /leP in H2. simpl. lia. }
{ move /leP in H1. move /leP in H2. simpl. lia. }
{ move /leP in H1. move /leP in H2. lia. } Qed.


Theorem bound_on_M
(M: list fill_type) (B:list Bid) (A:list Ask) (p:nat)
(NDB: NoDup B)(NDA: NoDup A):
(matching_in B A M) -> 
QM(M)<= QB(buyers_above p B) + QA(sellers_below p A).
Proof. intros. apply Mbgep_bound with (p:=p) in H as H1.
apply Mbltp_bound with (p:=p) in H as H2.
assert(QM(M) = QM(Mbgep p M) + QM(Mbltp p M)). 
apply M_bound_volume with (p:=p). lia. all:auto. Qed.



End Bound.