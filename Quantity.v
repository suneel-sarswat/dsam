

(*This file contains functions and their properties related to total quantities.*)




Require Import Wellfounded List Arith  Lia.
Require Import ssreflect ssrbool. 
Require Export Lists.List.
Require Export GenReflect SetSpecs.
Require Export DecSort MinMax.
Require Export mBidAsk.
Require Export DecList.



Section quantity.


(* Sum of total quantities of a bid and ask in fill_type and their properties *)

Fixpoint ttqb (F: list fill_type) (b:Bid) : (nat) :=
  match F with
  |nil => 0
  |f::F'=> match (b_eqb b (bid_of f)) with
      |true =>  (tq f)+(ttqb F' b)
      |false => (ttqb F' b)
  end
  end.
  
Lemma ttqb_elim (M:list fill_type) (b:Bid) : ~In b (bids_of M) -> ttqb M b = 0.
Proof. intros. induction M. simpl. auto. simpl in H. 
simpl. destruct (b_eqb b (bid_of a)) eqn: Hb. move /eqP in Hb. symmetry in Hb.
destruct H. left. auto. destruct IHM. intro. destruct H. right. exact H0.
auto. Qed.

Lemma ttqb_intro (M:list fill_type) (b:Bid)(NZT: forall m, In m M -> tq m>0): 
ttqb M b = 0 -> ~In b (bids_of M).
Proof. revert b. induction M. simpl. auto.
intros. simpl in H. destruct (b_eqb b (bid_of a)) eqn: Hb.
assert (tq a >0). eapply NZT. auto. lia. simpl.
intro. destruct H0.  subst b.  move /eqP in Hb. 
elim Hb. auto. revert H0. eapply IHM. auto. exact. Qed.
  
Fixpoint ttqa (F: list fill_type) (a:Ask) : (nat) :=
  match F with
  |nil => 0
  |f::F'=> match (a_eqb a (ask_of f)) with
      |true =>  (tq f)+(ttqa F' a)
      |false => (ttqa F' a)
  end
  end.

Lemma ttqa_elim (M:list fill_type) (a:Ask) : ~In a (asks_of M) -> ttqa M a = 0.
Proof. intros. induction M. simpl. auto. simpl in H. 
simpl. destruct (a_eqb a (ask_of a0)) eqn: Ha. move /eqP in Ha. symmetry in Ha.
destruct H. left. auto. destruct IHM. intro. destruct H. right. exact H0.
auto. Qed.

Lemma ttqa_intro (M:list fill_type) (a:Ask)(NZT: forall m, In m M -> tq m>0): 
ttqa M a = 0 -> ~In a (asks_of M).
Proof. revert a. induction M. simpl. auto.
intros. simpl in H. destruct (a_eqb a0 (ask_of a)) eqn: Hb.
assert (tq a >0). eapply NZT. auto. lia. simpl.
intro. destruct H0.  subst a0.  move /eqP in Hb. 
elim Hb. auto. revert H0. eapply IHM. auto. exact. Qed.




(*Total traded quanities of matching (list fill_type) *)

Fixpoint QM (M:list fill_type) :nat:=
match M with
|nil => 0
|m::M => tq m + QM M
end.

(*Sum of quantities of all the bids present in a list*)

Fixpoint QB (B:list Bid) :nat:=
match B with
|nil => 0
|b::B => bq b + QB B
end.


(*Sum of quantities of all the asks present in a list*)
Fixpoint QA (A:list Ask) :nat:=
match A with
|nil => 0
|a::A => sq a + QA A
end.


(*This function computes total traded quantity in a matching by computing total traded quantity of each ask. Note that QM and QMa are the same values and is being proved below *)
Fixpoint QMa (M:list fill_type)(A:list Ask):nat:=
match A with
|nil => 0
|a::A' => (ttqa M a) + QMa M A'
end.


(*This function computes total traded quantity in a matching by computing total traded quantity of each bid. Note that QM and QMb are the same values and is being proved below *)
Fixpoint QMb (M:list fill_type)(B:list Bid):nat:=
match B with
|nil => 0
|b::B' => (ttqb M b) + QMb M B'
end.



Lemma QMa_elim1 (M:list fill_type)(A:list Ask)(m:fill_type) (NDA:NoDup A):
~In (ask_of m) A-> QMa (m :: M) A = QMa M A.
Proof. revert m M. induction A as [|a A']. 
intros. simpl. auto. intros. simpl. destruct (a_eqb a (ask_of m)) eqn: Ham.
move /eqP in Ham. subst a. elim H. auto.  cut(QMa (m :: M) A' = QMa M A'). lia.
eapply IHA'. eauto. eauto. Qed.

Lemma QMa_elim2 (M:list fill_type)(A:list Ask)(m:fill_type)(NDA:NoDup A):
In (ask_of m) A -> QMa (m :: M) A = tq m + QMa M (A).
Proof. revert m M. induction A as [|a A'].  
{ simpl. intros. auto. } 
{ intros. destruct (a_eqb a (ask_of m)) eqn: Ham. destruct H. simpl. rewrite Ham.
rewrite QMa_elim1. eauto. rewrite <-H. eauto. lia. move /eqP in Ham. rewrite <-Ham in H.
assert(~In a A'). eauto. auto. destruct H. move /eqP in Ham. subst a. auto.
 simpl. rewrite Ham. rewrite IHA'. eauto. eauto. lia. } Qed.


Lemma QMb_elim1 (M:list fill_type)(B:list Bid)(m:fill_type) (NDB:NoDup B):
~In (bid_of m) B-> QMb (m :: M) B = QMb M B.
Proof. revert m M. induction B as [|b B']. 
intros. simpl. auto. intros. simpl. destruct (b_eqb b (bid_of m)) eqn: Hbm.
move /eqP in Hbm. subst b. elim H. auto.  cut(QMb (m :: M) B' = QMb M B'). lia.
eapply IHB'. eauto. eauto. Qed.

Lemma QMb_elim2 (M:list fill_type)(B:list Bid)(m:fill_type)(NDB:NoDup B):
In (bid_of m) B -> QMb (m :: M) B = tq m + QMb M (B).
Proof. revert m M. induction B as [|b B'].  
{ simpl. intros. auto. } 
{ intros. destruct (b_eqb b (bid_of m)) eqn: Hbm. destruct H. simpl. rewrite Hbm.
rewrite QMb_elim1. eauto. rewrite <-H. eauto. lia. move /eqP in Hbm. rewrite <-Hbm in H.
assert(~In b B'). eauto. auto. destruct H. move /eqP in Hbm. subst b. auto.
 simpl. rewrite Hbm. rewrite IHB'. eauto. eauto. lia. } Qed.


Lemma QM_equal_QMa (M:list fill_type)(A:list Ask) (NDA:NoDup A):
asks_of M [<=] A -> QMa M A = QM(M).
Proof. { 
revert A NDA. induction M as [|m M']. 
 { simpl. induction A. simpl. auto. simpl. intros. apply IHA.
eauto. eauto. }
 { induction A as [|a A']. 
   { simpl. intros. assert(In (ask_of m) nil). eauto. inversion H0. }
   { intros. destruct (a_eqb a (ask_of m)) eqn:Ham. 
                    { simpl. rewrite Ham. move /eqP in Ham. assert (asks_of M' [<=] a :: A').
                    eauto. eapply IHM' in H0. rewrite<- H0. simpl. 
                    cut(QMa (m :: M') A' = QMa M' A'). lia. eapply QMa_elim1. eauto.
                    rewrite<- Ham. eauto. eauto. }
                    { (*Prove more properties of QMa for different scenerios*)
                    assert(In a (asks_of M')\/~In a (asks_of M')). 
                    eauto. destruct H0.
                             2:{ simpl. rewrite Ham. eapply ttqa_elim in H0 as H1. 
                             rewrite H1.
                             rewrite IHA'. eauto. simpl in H. eapply subset_elim3 in H.
                              all:auto. move /eqP in Ham;auto. }
                             { cut(QMa M' (a :: A') = QM(M')). 
                              assert(QMa (m :: M') (a::A') = tq m + QMa M' (a::A')).
                              eapply QMa_elim2 with (A:=(a::A'))(M:=M')(m:=m).
                              eauto. simpl. right;auto. simpl in H. 
                              assert(In (ask_of m) (a::A')). eauto. destruct H1.
                              subst a. move /eqP in Ham. elim Ham. auto. auto.
                              rewrite H1. simpl. lia.
                             specialize (IHM' (a::A')). eapply IHM'. eauto. eauto. }}}}} 
                             Qed.
                              
Lemma QMa_equal_QMa (M1 M2:list fill_type)(A:list Ask):
(forall a, ttqa M1 a = ttqa M2 a) -> QMa M1 A = QMa M2 A.
Proof. induction A. simpl;auto. 
simpl. intro H.  specialize (H a) as Ha. rewrite Ha. rewrite IHA.
auto. auto. Qed.

Lemma QM_equal_QMb (M:list fill_type)(B:list Bid) (NDB:NoDup B):
bids_of M [<=] B -> QMb M B = QM(M).
Proof. { 
revert B NDB. induction M as [|m M']. 
 { simpl. induction B. simpl. auto. simpl. intros. apply IHB.
eauto. eauto. }
 { induction B as [|b B']. 
   { simpl. intros. assert(In (bid_of m) nil). eauto. inversion H0. }
   { intros. destruct (b_eqb b (bid_of m)) eqn:Hbm. 
                    { simpl. rewrite Hbm. move /eqP in Hbm. assert (bids_of M' [<=] b :: B').
                    eauto. eapply IHM' in H0. rewrite<- H0. simpl. 
                    cut(QMb (m :: M') B' = QMb M' B'). lia. eapply QMb_elim1. eauto.
                    rewrite<- Hbm. eauto. eauto. }
                    assert(In b (bids_of M')\/~In b (bids_of M')). 
                    eauto. destruct H0.
                             2:{ simpl. rewrite Hbm. eapply ttqb_elim in H0 as H1. 
                             rewrite H1.
                             rewrite IHB'. eauto. simpl in H. eapply subset_elim3 in H.
                              all:auto. move /eqP in Hbm;auto. }
                             { cut(QMb M' (b :: B') = QM(M')). 
                              assert(QMb (m :: M') (b::B') = tq m + QMb M' (b::B')).
                              eapply QMb_elim2 with (B:=(b::B'))(M:=M')(m:=m).
                              eauto. simpl. right;auto. simpl in H. 
                              assert(In (bid_of m) (b::B')). eauto. destruct H1.
                              subst b. move /eqP in Hbm. elim Hbm. auto. auto.
                              rewrite H1. simpl. lia.
                             specialize (IHM' (b::B')). eapply IHM'. eauto. eauto. }}}} 
                             Qed.
                              
Lemma QMb_equal_QMb (M1 M2:list fill_type)(B:list Bid):
(forall b, ttqb M1 b = ttqb M2 b) -> QMb M1 B = QMb M2 B.
Proof. induction B as [| b B]. simpl;auto. 
simpl. intro H.  specialize (H b) as Hb. rewrite Hb. rewrite IHB.
auto. auto. Qed.


Lemma ttqb_BM_t_B (M:list fill_type)(B:list Bid)(NDB:NoDup B) :
(bids_of M [<=] B)  -> 
(forall b, In b (bids_of M) -> ttqb M b <= bq b) ->(forall b, In b B -> ttqb M b <= bq b).
Proof. intros. assert(Hb: In b (bids_of M) \/~In b (bids_of M)). eauto.
destruct Hb. apply H0. auto. apply ttqb_elim in H2. lia. Qed.

Lemma fill_size_vs_bid_size (M:list fill_type)(B:list Bid)(NDB:NoDup B):
(forall b, In b B -> ttqb M b <= bq b) -> QMb M B <=QB(B).
Proof. revert M. induction B as [|b B'].
{ intros. simpl. auto. }
{ intros. simpl. assert(H0: ttqb M b <= bq b).  eapply H with (b0:=b). auto.
  cut(QMb M B' <= QB B'). lia.  eapply IHB'. eauto. auto. } Qed.
  

Lemma ttqaM1_equal_ttqaM2 (M1 M2:list fill_type)(A:list Ask)(NDA: NoDup A):
asks_of M1 [<=] A -> asks_of M2 [<=] A -> (forall a, ttqa M1 a = ttqa M2 a) -> QM M1 = QM M2.
Proof. intros. eapply QM_equal_QMa in H;eapply QM_equal_QMa in H0. 
eapply QMa_equal_QMa with (A:=A) in H1. lia. all:exact. Qed.





End quantity.
