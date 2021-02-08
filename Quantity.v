

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


Lemma ttqb_intro1 (M:list fill_type) (b:Bid): 
ttqb M b <> 0 -> In b (bids_of M).
Proof. revert b. induction M. simpl. auto.
intros. simpl in H. destruct (b_eqb b (bid_of a)) eqn: Hb. simpl.
move /eqP in Hb. subst. auto. apply IHM in H. simpl. auto. Qed.


Lemma ttqb_delete_m_ofb 
(M:list fill_type) (m:fill_type) (b:Bid) : 
In m M -> b=bid_of m -> ttqb M b = ttqb (delete m M) b + tq m.
Proof. intros. induction M as [|m' M']. elim H. 
simpl. destruct (b_eqb b (bid_of m')) eqn: Hb.
destruct H. subst m.
replace (m_eqb m' m') with true. lia. auto. 
destruct (m_eqb m m') eqn:Hmm.
move /eqP in Hmm. subst m. lia. 
simpl. rewrite Hb. rewrite IHM'.
auto. lia.
destruct H. subst m. subst b.
move /eqP in Hb. elim Hb. auto. 
simpl.
destruct (m_eqb m m') eqn:Hmm.
move /eqP in Hmm. subst m. subst b.
move /eqP in Hb. elim Hb. auto. 
simpl.
rewrite Hb. rewrite IHM'.
auto. lia. Qed.

Lemma ttqb_delete_m_not_ofb 
(M:list fill_type) (m:fill_type) (b:Bid) : 
In m M -> b<>bid_of m -> ttqb M b = ttqb (delete m M) b.
Proof. intros. induction M as [|m' M']. elim H. 
simpl. destruct (b_eqb b (bid_of m')) eqn: Hb.
destruct H. subst m.
move /eqP in Hb. subst b.
elim H0. auto. 
destruct (m_eqb m m') eqn:Hmm.
move /eqP in Hmm. subst m.
move /eqP in Hb. subst b.
elim H0. auto. 
simpl. rewrite Hb. rewrite IHM'.
auto. lia.
destruct H. subst m.
replace (m_eqb m' m' ) with true.
auto. eauto.
destruct (m_eqb m m') eqn:Hmm. auto.
simpl.
rewrite Hb. rewrite IHM'.
auto. lia. Qed.

Lemma ttqb_equal_implies_subet (M1 M2:list fill_type)
(NZT:forall m : fill_type, In m M1 -> tq m > 0): 
(forall b, ttqb M1 b = ttqb M2 b) -> (bids_of M1) [<=] (bids_of M2).
Proof. unfold "[<=]".
       intros. assert(In a (bids_of M2)\/~In a (bids_of M2)).
       eauto. destruct H1. auto.
       specialize (H a).
       apply ttqb_elim in H1. rewrite H1 in H.
       apply ttqb_intro in H. unfold not in H.
       apply H in H0. elim H0. eauto. Qed.

Lemma ttqb_of_perm (M1 M2:list fill_type)
(*(NZT:forall m : fill_type, In m M1 -> tq m > 0)*): 
perm M1 M2 -> (forall b, ttqb M1 b = ttqb M2 b).
Proof. Proof. revert M2. induction M1. 
intros. unfold perm in H. 
move /andP in H. destruct H.
assert(M2=nil).
eauto. rewrite H1. auto.
intros. unfold perm in H. 
move /andP in H. destruct H.
simpl. destruct(b_eqb b (bid_of a)) eqn:Ha. 
{
move /eqP in Ha.
assert(In a M2). eauto.
eapply ttqb_delete_m_ofb with (M:=M2) in Ha.
rewrite Ha. cut(ttqb M1 b = ttqb (delete a M2) b).
lia. 
apply included_elim3a with (a0:=a) in H.
simpl in H. replace (m_eqb a a) with true in H.
apply included_elim3a with (a0:=a) in H0.
simpl in H0. replace (m_eqb a a) with true in H0. 
assert(perm M1 (delete a M2)). 
unfold perm. apply /andP. auto.
apply IHM1 with (b:=b) in H2. lia. 
eauto. eauto. eauto.
}
{ move /eqP in Ha. eapply ttqb_delete_m_not_ofb with (M:=M2) in Ha.
apply included_elim3a with (a0:=a) in H.
simpl in H. replace (m_eqb a a) with true in H.
apply included_elim3a with (a0:=a) in H0.
simpl in H0. replace (m_eqb a a) with true in H0. 
assert(perm M1 (delete a M2)). 
unfold perm. apply /andP. auto. rewrite Ha.
apply IHM1 with (b:=b) in H1. lia. 
eauto. eauto. eauto.
} Qed.


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

Lemma ttqa_intro1 (M:list fill_type) (a:Ask): 
ttqa M a <> 0 -> In a (asks_of M).
Proof. revert a. induction M. simpl. auto.
intros. simpl in H. destruct (a_eqb a0 (ask_of a)) eqn: Hb. simpl.
move /eqP in Hb. subst a0. auto. apply IHM in H. simpl. auto. Qed.


Lemma ttqa_delete_m_ofa 
(M:list fill_type) (m:fill_type) (a:Ask) : 
In m M -> a=ask_of m -> ttqa M a = ttqa (delete m M) a + tq m.
Proof. intros. induction M as [|m' M']. elim H. 
simpl. destruct (a_eqb a (ask_of m')) eqn: Ha.
destruct H. subst m.
replace (m_eqb m' m') with true. lia. auto. 
destruct (m_eqb m m') eqn:Hmm.
move /eqP in Hmm. subst m. lia. 
simpl. rewrite Ha. rewrite IHM'.
auto. lia.
destruct H. subst m. subst a.
move /eqP in Ha. elim Ha. auto. 
simpl.
destruct (m_eqb m m') eqn:Hmm.
move /eqP in Hmm. subst m. subst a.
move /eqP in Ha. elim Ha. auto. 
simpl.
rewrite Ha. rewrite IHM'.
auto. lia. Qed.

Lemma ttqa_delete_m_not_ofa 
(M:list fill_type) (m:fill_type) (a:Ask) : 
In m M -> a<>ask_of m -> ttqa M a = ttqa (delete m M) a.
Proof. intros. induction M as [|m' M']. elim H. 
simpl. destruct (a_eqb a (ask_of m')) eqn: Ha.
destruct H. subst m.
move /eqP in Ha. subst a.
elim H0. auto. 
destruct (m_eqb m m') eqn:Hmm.
move /eqP in Hmm. subst m.
move /eqP in Ha. subst a.
elim H0. auto. 
simpl. rewrite Ha. rewrite IHM'.
auto. lia.
destruct H. subst m.
replace (m_eqb m' m' ) with true.
auto. eauto.
destruct (m_eqb m m') eqn:Hmm. auto.
simpl.
rewrite Ha. rewrite IHM'.
auto. lia. Qed.

Lemma ttqa_equal_implies_subet (M1 M2:list fill_type)
(NZT:forall m : fill_type, In m M1 -> tq m > 0): 
(forall a, ttqa M1 a = ttqa M2 a) -> (asks_of M1) [<=] (asks_of M2).
Proof. unfold "[<=]".
       intros. assert(In a (asks_of M2)\/~In a (asks_of M2)).
       eauto. destruct H1. auto.
       specialize (H a).
       apply ttqa_elim in H1. rewrite H1 in H.
       apply ttqa_intro in H. unfold not in H.
       apply H in H0. elim H0. eauto. Qed.
        
Lemma ttqa_of_perm (M1 M2:list fill_type)
(*(NZT:forall m : fill_type, In m M1 -> tq m > 0)*): 
perm M1 M2 -> (forall a, ttqa M1 a = ttqa M2 a).
Proof. Proof. revert M2. induction M1. 
intros. unfold perm in H. 
move /andP in H. destruct H.
assert(M2=nil).
eauto. rewrite H1. auto.
intros. unfold perm in H. 
move /andP in H. destruct H.
simpl. destruct(a_eqb a0 (ask_of a)) eqn:Ha. 
{
move /eqP in Ha.
assert(In a M2). eauto.
eapply ttqa_delete_m_ofa with (M:=M2) in Ha.
rewrite Ha. cut(ttqa M1 a0 = ttqa (delete a M2) a0).
lia. 
apply included_elim3a with (a1:=a) in H.
simpl in H. replace (m_eqb a a) with true in H.
apply included_elim3a with (a1:=a) in H0.
simpl in H0. replace (m_eqb a a) with true in H0. 
assert(perm M1 (delete a M2)). 
unfold perm. apply /andP. auto.
apply IHM1 with (a:=a0) in H2. lia. 
eauto. eauto. eauto.
}
{ move /eqP in Ha. eapply ttqa_delete_m_not_ofa with (M:=M2) in Ha.
apply included_elim3a with (a1:=a) in H.
simpl in H. replace (m_eqb a a) with true in H.
apply included_elim3a with (a1:=a) in H0.
simpl in H0. replace (m_eqb a a) with true in H0. 
assert(perm M1 (delete a M2)). 
unfold perm. apply /andP. auto. rewrite Ha.
apply IHM1 with (a:=a0) in H1. lia. 
eauto. eauto. eauto.
} Qed.


Fixpoint ttq_ab (F: list fill_type) (b:Bid)(a:Ask) : (nat) :=
  match F with
  |nil => 0
  |f::F'=> match ((a_eqb a (ask_of f)) && (b_eqb b (bid_of f))) with
                |true => (tq f)+(ttq_ab F' b a)
                |false => (ttq_ab F' b a)
  end
end.

Hint Immediate ttqb_elim ttqa_elim: core.
Hint Resolve ttqb_intro ttqa_intro : core.
Hint Resolve ttqb_delete_m_not_ofb ttqb_delete_m_ofb : core.
Hint Resolve ttqa_delete_m_not_ofa ttqa_delete_m_ofa : core.

Lemma ttq_ab_elim_a (M:list fill_type)(b:Bid) (a:Ask) :
~In a (asks_of M) -> ttq_ab M b a = 0.
Proof. intros. induction M. { simpl. auto. }
{ simpl in H. 
simpl. destruct (a_eqb a (ask_of a0) && b_eqb b (bid_of a0)) eqn: Hab.
{ move /andP in Hab. 
destruct Hab.   move /eqP in H0. 
 move /eqP in H1. destruct H. left. auto. }
{ apply IHM. revert H. eauto. } } Qed.


Lemma ttq_ab_elim_b (M:list fill_type)(b:Bid) (a:Ask) :
~In b (bids_of M) -> ttq_ab M b a = 0.
Proof. intros. induction M. { simpl. auto. }
{ simpl in H. 
simpl. destruct (a_eqb a (ask_of a0) && b_eqb b (bid_of a0)) eqn: Hab.
{ move /andP in Hab. 
destruct Hab.   move /eqP in H0. 
 move /eqP in H1. destruct H. left. auto. }
{ apply IHM. revert H. eauto. } } Qed.


Hint Resolve ttq_ab_elim_b ttq_ab_elim_a : core.

Lemma ttqa_intro_ba (M:list fill_type) (b:Bid)(a:Ask)(NZT: forall m, In m M -> tq m>0): 
ttq_ab M b a = 0 -> (forall m, In m M ->(b=bid_of m -> a<>ask_of m)).
Proof. revert a b. induction M. 
{ simpl. auto. }
{
intros. simpl in H. 
destruct (a_eqb a0 (ask_of a) && b_eqb b (bid_of a)) eqn: Hab.
{
assert (tq a >0). eapply NZT. auto.
  lia. }
  destruct H0.
  subst a.  move /andP in Hab. subst b. eauto.
  
  apply IHM with (m:=m) in H. auto. auto.
  auto. auto. } Qed.

Lemma ttqa_intro_ab (M:list fill_type)(b:Bid) (a:Ask)(NZT: forall m, In m M -> tq m>0): 
ttq_ab M b a = 0 -> (forall m, In m M ->(a=ask_of m -> b<>bid_of m)).

Proof. revert a b. induction M. 
{ simpl. auto. }
{
intros. simpl in H. 
destruct (a_eqb a0 (ask_of a) && b_eqb b (bid_of a)) eqn: Hab.
{
assert (tq a >0). eapply NZT. auto.
  lia. }
  destruct H0.
  subst a.  move /andP in Hab. subst a0. eauto.
  
  apply IHM with (m:=m) in H. auto. auto.
  auto. auto. } Qed.
  

Hint Immediate ttqa_intro_ab ttqa_intro_ba: core.

Lemma ttq_ab_le_ttqa (M:list fill_type)(b:Bid)(a:Ask): 
ttq_ab M b a <= ttqa M a.
Proof. revert a. induction M. intros. simpl. auto.
intros. simpl. 
destruct (a_eqb a0 (ask_of a)) eqn:Ha0a;destruct (b_eqb b (bid_of a)) eqn: Hba.
{ simpl. cut(ttq_ab M b a0 <= ttqa M a0). lia. eapply IHM. }
{ simpl. cut(ttq_ab M b a0 <= ttqa M a0). lia. eapply IHM. }
{ simpl. eapply IHM. }
{ simpl. eapply IHM. }
Qed. 


Lemma ttq_ab_le_ttqb (M:list fill_type)(b:Bid)(a:Ask): 
ttq_ab M b a <= ttqb M b.
Proof. revert a. induction M. intros. simpl. auto.
intros. simpl. 
destruct (a_eqb a0 (ask_of a)) eqn:Ha0a;destruct (b_eqb b (bid_of a)) eqn: Hba.
{ simpl. cut(ttq_ab M b a0 <= ttqb M b). lia. eapply IHM. }
{ simpl.  eapply IHM. }
{ simpl. cut(ttq_ab M b a0 <= ttqb M b). lia. eapply IHM. }
{ simpl. eapply IHM. }
Qed.

Lemma ttq_ab_delete (M:list fill_type)(b:Bid)(a:Ask)(m:fill_type): 
In m M -> (b<>bid_of m)\/(a<>ask_of m) -> ttq_ab M b a = ttq_ab (delete m M) b a.
Proof.  revert a b m. induction M as [|m' M'].
{ simpl. intros. elim H. }
{ intros. destruct H0.
  { destruct H. 
    { subst m'. simpl. destruct (b_eqb b (bid_of m)) eqn:Hbm.
      move /eqP in Hbm. subst b. elim H0. auto.
      destruct (a_eqb a (ask_of m)). simpl. replace (m_eqb m m) with true.
      auto. eauto. simpl. replace (m_eqb m m) with true. auto.
      eauto. 
     }
     { simpl. 
       destruct (a_eqb a (ask_of m') && b_eqb b (bid_of m')) eqn: Habm.
       destruct (m_eqb m m') eqn:Hmm. move /eqP in Hmm.
       subst m. move /andP in Habm.  destruct Habm. 
       move /eqP in H2.  subst b.  elim H0.  auto. 
       simpl. rewrite Habm. 
        eapply IHM' with (a:=a)(b:=b) in H. lia.
        left.  auto.
       destruct (m_eqb m m') eqn:Hmm. auto. simpl. 
        rewrite Habm. 
        eapply IHM' with (a:=a)(b:=b) in H. lia.
        left.  auto.
      }
  }
  { destruct H. 
    {
      subst m'. simpl. destruct (a_eqb a (ask_of m)) eqn:Hbm.
      move /eqP in Hbm. subst a. elim H0. auto.
      destruct (b_eqb b (bid_of m)). simpl. replace (m_eqb m m) with true.
      auto. eauto. simpl. replace (m_eqb m m) with true. auto.
      eauto. 
     }
     { simpl. 
       destruct (a_eqb a (ask_of m') && b_eqb b (bid_of m')) eqn: Habm.
       destruct (m_eqb m m') eqn:Hmm. move /eqP in Hmm.
       subst m. move /andP in Habm.  destruct Habm. 
       move /eqP in H1.  subst a.  elim H0.  auto. 
       simpl. rewrite Habm. 
       eapply IHM' with (a:=a)(b:=b) in H. lia.
        right.  auto.
       destruct (m_eqb m m') eqn:Hmm. auto. simpl. 
        rewrite Habm. 
        eapply IHM' with (a:=a)(b:=b) in H. lia.
        right.  auto.
      
     }
  }
  }
  Qed.
   

Hint Resolve ttq_ab_le_ttqb ttq_ab_le_ttqa : core.

Lemma b_in_a_out_m_exists (M:list fill_type)(b:Bid)(a:Ask):
ttqa M a >= ttq_ab M b a ->
ttqb M b > ttq_ab M b a ->
exists m : fill_type,
  In m M /\ bid_of m = b /\ ask_of m <> a.
  Proof. 
  { 
    revert a b. induction M as [|m' M'].
    simpl. intros. lia. 
    simpl. intros. 
    destruct (a_eqb a (ask_of m')) eqn: Ham;
    destruct (b_eqb b (bid_of m')) eqn: Hbm.
    { simpl in H. simpl in H0. 
      assert(Hm: exists m : fill_type, 
      (In m M') /\ bid_of m = b /\ ask_of m <> a).
      apply IHM' with (a:=a)(b:=b). lia. lia.
      destruct Hm as [m0 Hm]. 
      exists m0. split. right. apply Hm. apply Hm. 
    }
    { 
     simpl in H. simpl in H0. 
     assert(Hm: exists m : fill_type, 
     (In m M') /\ bid_of m = b /\ ask_of m <> a).
     apply IHM' with (a:=a)(b:=b). 
     assert (ttq_ab M' b a <= ttqa M' a). eauto. lia. lia.
     destruct Hm as [m0 Hm]. 
     exists m0. split. right. apply Hm. apply Hm. 
    }
    {
    exists m'. split. left. auto. move /eqP in Ham. 
    move /eqP in Hbm. auto.  
    }
    {
     simpl in H. simpl in H0. 
     assert(Hm: exists m : fill_type, 
     (In m M') /\ bid_of m = b /\ ask_of m <> a).
     apply IHM' with (a:=a)(b:=b). 
     lia. lia.
     destruct Hm as [m0 Hm]. 
     exists m0. split. right. apply Hm. apply Hm.
    }
  } Qed.
  

Lemma a_in_b_out_m_exists  (M:list fill_type)(b:Bid)(a:Ask):
ttqa M a > ttq_ab M b a ->
ttqb M b >= ttq_ab M b a ->
exists m : fill_type,
  In m M /\ ask_of m = a /\ bid_of m <> b.
  Proof. 
  { 
    revert a b. induction M as [|m' M'].
    simpl. intros. lia. 
    simpl. intros. 
    destruct (a_eqb a (ask_of m')) eqn: Ham;
    destruct (b_eqb b (bid_of m')) eqn: Hbm.
    { simpl in H. simpl in H0. 
      assert(Hm: exists m : fill_type, 
      (In m M') /\ ask_of m = a /\ bid_of m <> b).
      apply IHM' with (a:=a)(b:=b). lia. lia.
      destruct Hm as [m0 Hm]. 
      exists m0. split. right. apply Hm. apply Hm. 
    }
    {
    exists m'. split. left. auto. move /eqP in Ham. 
    move /eqP in Hbm. auto.  
    }
    { 
     simpl in H. simpl in H0. 
     assert(Hm: exists m : fill_type, 
     (In m M') /\ ask_of m = a /\ bid_of m <> b).
     apply IHM' with (a:=a)(b:=b). lia.
     assert (ttq_ab M' b a <= ttqb M' b). eauto. lia.
     destruct Hm as [m0 Hm]. 
     exists m0. split. right. apply Hm. apply Hm. 
    }
    {
     simpl in H. simpl in H0. 
     assert(Hm: exists m : fill_type, 
     (In m M') /\ ask_of m = a /\ bid_of m <> b).
     apply IHM' with (a:=a)(b:=b). 
     lia. lia.
     destruct Hm as [m0 Hm]. 
     exists m0. split. right. apply Hm. apply Hm.
    }
  } Qed.

  

Hint Resolve a_in_b_out_m_exists b_in_a_out_m_exists :core.
(*Total traded quanities of matching (list fill_type) *)

Fixpoint QM (M:list fill_type) :nat:=
match M with
|nil => 0
|m::M => tq m + QM M
end.

Lemma QM_elim0 (M:list fill_type) (m :fill_type):
In m M -> QM(M) >= (tq m).
Proof.  induction M. simpl. intros. elim H.
intros. simpl. destruct H. subst a. lia.
cut(QM M >= tq m). lia. apply IHM. auto. Qed.

Lemma QM_elim1 (M:list fill_type) (m :fill_type):
In m M -> QM(delete m M) =QM(M) - (tq m).
Proof.  induction M as [| m' M']. simpl. auto.
simpl. destruct (m_eqb m m') eqn:Hmm.
move /eqP in Hmm. subst m. lia.
simpl. intros.  move /eqP in Hmm.
destruct H. subst m. elim Hmm. auto.
rewrite IHM'. auto. assert(QM M' >= tq m).
apply QM_elim0. auto. lia. Qed.

Lemma QM_elim2 (M:list fill_type) (m1 m2:fill_type):
m1<>m2 -> In m1 M -> In m2 M -> QM M >= tq m1 + tq m2.
Proof.
induction M. simpl.
intros H0 H. elim H. intros.
destruct H0;destruct H1.
{
subst a. subst m1. elim H. auto. 
}
{ simpl. subst a. cut(QM M >= tq m2). lia.
  apply QM_elim0. auto.
}
{ 
simpl. subst a. cut(QM M >= tq m1). lia.
  apply QM_elim0. auto.
}
{ simpl. cut(QM M >= tq m1 + tq m2). lia.
apply IHM. auto. auto. auto.
} 
Qed.
    
Lemma QM_perm (M1 M2:list fill_type):
perm M1 M2 -> QM(M1) = QM(M2).
Proof. revert M2. induction M1. 
intros. unfold perm in H. 
move /andP in H. destruct H.
assert(M2=nil).
eauto. rewrite H1. auto.
intros. unfold perm in H. 
move /andP in H. destruct H.
simpl. assert(In a M2). eauto.
assert(QM(delete a M2) =QM(M2) - (tq a)).
apply QM_elim1. auto. 
apply included_elim3a with (a0:=a) in H.
simpl in H. replace (m_eqb a a) with true in H.
apply included_elim3a with (a0:=a) in H0.
simpl in H0. replace (m_eqb a a) with true in H0. 
assert(perm M1 (delete a M2)). 
unfold perm. apply /andP. auto.
apply IHM1 in H3. 
apply QM_elim0 in H1. lia. eauto. eauto. Qed.

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

Hint Resolve QMb_elim1 QMb_elim2 QMa_elim1 QMb_elim2: core.


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


Lemma ttqa_AM_t_A (M:list fill_type)(A:list Ask)(NDA:NoDup A) :
(asks_of M [<=] A)  -> 
(forall a, In a (asks_of M) -> ttqa M a <= sq a) ->(forall a, In a A -> ttqa M a <= sq a).
Proof. intros. assert(Ha: In a (asks_of M) \/~In a (asks_of M)). eauto.
destruct Ha. apply H0. auto. apply ttqa_elim in H2. lia. Qed.

Lemma fill_size_vs_ask_size (M:list fill_type)(A:list Ask)(NDA:NoDup A):
(forall a, In a A -> ttqa M a <= sq a) -> QMa M A <=QA(A).
Proof. revert M. induction A as [|a A'].
{ intros. simpl. auto. }
{ intros. simpl. assert(H0: ttqa M a <= sq a).  eapply H with (a0:=a). auto.
  cut(QMa M A' <= QA A'). lia.  eapply IHA'. eauto. auto. } Qed.
  

Lemma ttqbM1_equal_ttqbM2 (M1 M2:list fill_type)(B:list Bid)(NDB: NoDup B):
bids_of M1 [<=] B -> bids_of M2 [<=] B -> (forall b, ttqb M1 b = ttqb M2 b) -> QM M1 = QM M2.
Proof. intros. eapply QM_equal_QMb in H;eapply QM_equal_QMb in H0. 
eapply QMb_equal_QMb with (B:=B) in H1. lia. all:exact. Qed.


Hint Resolve 
QM_equal_QMa QMa_equal_QMa QM_equal_QMb QMb_equal_QMb
 fill_size_vs_bid_size ttqaM1_equal_ttqaM2 ttqb_BM_t_B ttqa_AM_t_A
  fill_size_vs_ask_size ttqbM1_equal_ttqbM2: core.



End quantity.

Hint Immediate ttqa_intro_ab ttqa_intro_ba: core.
Hint Immediate ttqb_elim ttqa_elim: core.
Hint Resolve a_in_b_out_m_exists b_in_a_out_m_exists :core.
Hint Immediate ttqb_BM_t_B ttqa_AM_t_A : core.
Hint Resolve ttqb_intro ttqa_intro : core.
Hint Resolve QM_elim0 QM_elim1 QM_perm : core.
Hint Resolve ttq_ab_elim_b ttq_ab_elim_a : core.
Hint Resolve ttq_ab_le_ttqb ttq_ab_le_ttqa : core.
Hint Resolve QM_equal_QMa QMa_equal_QMa QM_equal_QMb QMb_equal_QMb
 fill_size_vs_bid_size ttqaM1_equal_ttqaM2 
  fill_size_vs_ask_size ttqbM1_equal_ttqbM2: core.
Hint Resolve ttqb_delete_m_not_ofb ttqb_delete_m_ofb : core.
Hint Resolve ttqa_delete_m_not_ofa ttqa_delete_m_ofa : core.
