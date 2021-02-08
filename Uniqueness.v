Require Import ssreflect ssrbool.
Require Export Lists.List.
Require Export GenReflect SetSpecs.
Require Export DecList.
Require Export DecSort.
Require Export mBidAsk.
Require Export Quantity.
Require Export mMatching.
Require Export MatchingAlter.
Require Export MQFair.


Section Uniqueness.

(*
Definition Optimal_IR_Uniform (M:list fill_type)(B:list Bid)(A:list Ask): 
matching_in B A M/\ Is_IR M /\ Uniform M/\(forall M', (matching_in B A M'/\Is_IR M' /\ Uniform M') -> QM(M')<=QM(M)).
*)
Lemma less_Q_implies_less_qa (M1 M2: list fill_type)(A:list Ask):
QMa M1 A < QMa M2 A ->
exists a' : Ask, (In a' A)/\(ttqa M1 a' < ttqa M2 a').
Proof. revert M1 M2. induction A. intros. simpl in H.
lia. intros. simpl in H. 
assert(Ha:(ttqa M1 a < ttqa M2 a)\/(ttqa M1 a >= ttqa M2 a)).
lia. destruct Ha. exists a. auto. assert(QMa M1 A < QMa M2 A).
lia. apply IHA in H1. destruct H1. destruct H1. exists x. auto. Qed.

Lemma size_equal_and_gt_imply_lt_ask (M1 M2: list fill_type)(A:list Ask)
(a:Ask):
(QMa M1 A = QMa M2 A) -> In a A -> (ttqa M1 a > ttqa M2 a) -> 
(exists a', (In a' A)/\(ttqa M1 a' < ttqa M2 a')).

Proof. intros. 
       induction A. elim H0. 
       simpl in H0. destruct H0. subst a0.
       simpl in H. assert(HM:QMa M1 A < QMa M2 A).
       lia. apply less_Q_implies_less_qa with (A:=A) in HM.
       destruct HM. destruct H0. exists x. auto.
       simpl in H.
       assert(Ha:(ttqa M1 a0 < ttqa M2 a0)
       \/(ttqa M1 a0 = ttqa M2 a0)
       \/(ttqa M1 a0 > ttqa M2 a0)).
       lia.
       destruct Ha.
       exists a0. auto.
       destruct H2.
       assert(QMa M1 A = QMa M2 A).
       lia. apply IHA in H3.
       destruct H3. destruct H3. exists x. auto.
       auto.
       assert(QMa M1 A < QMa M2 A). lia.
       apply less_Q_implies_less_qa with (A:=A) in H3.
       destruct H3. destruct H3. exists x. auto. Qed.
        



Lemma Qsize_equal_and_gt_imply_lt_ask (M1 M2: list fill_type)(A:list Ask)
(NDA: NoDup A)(a:Ask):
(QM(M1) = QM(M2)) -> (ttqa M1 a > ttqa M2 a) -> asks_of M1 [<=] A
-> asks_of M2 [<=] A ->
(exists a', (In a' A)/\(ttqa M1 a' < ttqa M2 a')).
Proof. intros. apply QM_equal_QMa in H1 as H3. apply QM_equal_QMa in H2 as H4.
       rewrite <- H3 in H. rewrite <- H4 in H.
       assert(Ha1:In a (asks_of M1)). apply ttqa_intro1. lia.
       assert (Ha2: In a A). eauto.
       apply size_equal_and_gt_imply_lt_ask with (a:=a). all:auto. Qed. 
       


Theorem completeness_asks (M1 M2: list fill_type) (B:list Bid) (A:list Ask)
(NZB: forall b, In b B -> (bq b)>0)
(NZA: forall a, In a A -> (sq a)>0)
(NDA: NoDup A)(a:Ask):
  (matching_in B A M1)/\ (matching_in B A M2) 
  /\(QM(M1) = QM(M2))
  /\(fair_on_asks M1 A) /\ (fair_on_asks M2 A)
    -> (ttqa M1 a = ttqa M2 a).
Proof. intros. destruct H. destruct H0. destruct H1. destruct H2. 
unfold fair_on_asks in H2. unfold fair_on_asks in H3.
assert(Hta:ttqa M1 a = ttqa M2 a\/ttqa M1 a <> ttqa M2 a).
eauto. destruct Hta. auto.
assert(Hga:ttqa M1 a > ttqa M2 a\/ttqa M1 a < ttqa M2 a).
 lia. destruct Hga. 
  (*Case when there exists an ask a such that it's total trade quantities is more in M1 than M2*)
  { assert(exists a', (In a' A)/\(ttqa M1 a' < ttqa M2 a')).
    {  
      apply Qsize_equal_and_gt_imply_lt_ask with (a:=a). all:auto.
      apply H. apply H0.
    }
    destruct H6 as [a' H6]. destruct H6.
    assert(Ha: (by_sp a a')\/(by_sp a' a)). apply by_sp_P.
    destruct Ha. 
    (*Case when a is more competitive ask than a' *)
    { assert(ttqa M2 a = 0\/ttqa M2 a <>0) by eauto.
      destruct H9.  (*Case when more competitive does not belongs to M2*)
        { destruct (a_eqb a a') eqn:Haa'. move /eqP in Haa'. subst. lia.
          assert(HqaM1: ttqa M1 a>0). lia. assert(HM1A:In a (asks_of M1)). 
          { apply ttqa_intro1. lia. }
          assert(HA:In a A). apply H in  HM1A. auto. 
          assert(HqaM2: ttqa M2 a'>0). lia. assert(HM2A:In a' (asks_of M2)). 
          { apply ttqa_intro1. lia. }
          assert(HA2:In a' A). apply H0 in  HM2A. auto.
          apply H3 in H8. destruct H8. specialize (NZA a). 
          apply NZA in  HA. lia. auto. move /eqP in Haa'.  auto. 
          auto. lia. 
        } (*Case when more competitive belongs to M2*)
        { assert(ttqa M1 a = 0\/ttqa M1 a <>0) by eauto.
          destruct H10.
          { lia. }
          { destruct (a_eqb a a') eqn:Haa'. move /eqP in Haa'. subst. lia.
            assert(HqaM1: ttqa M1 a>0). lia. assert(HM1A:In a (asks_of M1)). 
            { apply ttqa_intro1. lia. }
            assert(HA:In a A). apply H in  HM1A. auto. 
            assert(HqaM2: ttqa M2 a'>0). lia. assert(HM2A:In a' (asks_of M2)). 
            { apply ttqa_intro1. lia. }
            assert(HA2:In a' A). apply H0 in  HM2A. auto.
            assert(ttqa M2 a' >0) by lia. 
            apply H3 with (s:=a)(s':=a') in H11 as H13.
            destruct H13. assert(ttqa M1 a <= sq a). apply H.
            auto. lia. 
            all:auto. move /eqP in Haa'. auto.
          }
        }
      }
    (*Case when a' is more competitive ask than a *)
    { assert(ttqa M1 a' = 0\/ttqa M1 a' <>0) by eauto.
      destruct H9.  (*Case when more competitive does not belongs to M1*)
        { destruct (a_eqb a a') eqn:Haa'. move /eqP in Haa'. subst. lia.
          assert(HqaM1: ttqa M2 a'>0). lia. assert(HM2A:In a' (asks_of M2)). 
          { apply ttqa_intro1. lia. }
          assert(HA:In a' A). apply H0 in HM2A. auto. 
          assert(HqaM2: ttqa M1 a>0). lia. assert(HM1A:In a (asks_of M1)). 
          { apply ttqa_intro1. lia. }
          assert(HA2:In a A). apply H in  HM1A. auto.
          apply H2 in H8. destruct H8. specialize (NZA a'). 
          apply NZA in  HA. lia. auto. move /eqP in Haa'.  auto. 
          auto. lia. 
        } (*Case when more competitive belongs to M2*)
        { assert(ttqa M2 a' = 0\/ttqa M2 a' <>0) by eauto.
          destruct H10.
          { lia. }
          { destruct (a_eqb a a') eqn:Haa'. move /eqP in Haa'. subst. lia.
            assert(HqaM1: ttqa M2 a'>0). lia. assert(HM2A:In a' (asks_of M2)). 
            { apply ttqa_intro1. lia. }
            assert(HA:In a' A). apply H0 in HM2A. auto. 
            assert(HqaM2: ttqa M1 a>0). lia. assert(HM1A:In a (asks_of M1)). 
            { apply ttqa_intro1. lia. }
            assert(HA2:In a A). apply H in  HM1A. auto.
            apply H2 with (s:=a')(s':=a) in H8 as H12. destruct H12.
            assert(ttqa M2 a' <= sq a'). apply H0.
            auto. lia. 
            all:auto. move /eqP in Haa'. auto.
          }
        }
      }
    }
      (*Case when there exists an ask a such that it's total trade quantities is more in M1 than M2*)
  { assert(exists a', (In a' A)/\(ttqa M1 a' > ttqa M2 a')).
    {  
      apply Qsize_equal_and_gt_imply_lt_ask with (a:=a). all:auto.
      apply H0. apply H.
    }
    destruct H6 as [a' H6]. destruct H6.
    assert(Ha: (by_sp a a')\/(by_sp a' a)). apply by_sp_P.
    destruct Ha. 
    (*Case when a is more competitive ask than a' *)
    { assert(ttqa M1 a = 0\/ttqa M1 a <>0) by eauto.
      destruct H9.  (*Case when more competitive does not belongs to M2*)
        { destruct (a_eqb a a') eqn:Haa'. move /eqP in Haa'. subst. lia.
          assert(HqaM2: ttqa M2 a>0). lia. assert(HM2A:In a (asks_of M2)). 
          { apply ttqa_intro1. lia. }
          assert(HA:In a A). apply H0 in  HM2A. auto. 
          assert(HqaM1: ttqa M1 a'>0). lia. assert(HM1A:In a' (asks_of M1)). 
          { apply ttqa_intro1. lia. }
          assert(HA2:In a' A). apply H0 in HM2A. auto.
          eapply H2 with (s:=a) in HqaM1. destruct HqaM1. specialize (NZA a). 
          apply NZA in  HA. lia. auto. move /eqP in Haa'.  auto. 
          auto. auto. 
        } (*Case when more competitive belongs to M2*)
        { assert(ttqa M2 a = 0\/ttqa M2 a <>0) by eauto.
          destruct H10.
          { lia. }
          { destruct (a_eqb a a') eqn:Haa'. move /eqP in Haa'. subst. lia.
            assert(HqaM2: ttqa M2 a>0). lia. assert(HM2A:In a (asks_of M2)). 
            { apply ttqa_intro1. lia. }
            assert(HA:In a A). apply H0 in  HM2A. auto. 
            assert(HqaM1: ttqa M1 a'>0). lia. assert(HM1A:In a' (asks_of M1)). 
            { apply ttqa_intro1. lia. }
            assert(HA2:In a' A). apply H0 in HM2A. auto.
            apply H2 with (s:=a)(s':=a') in HqaM1 as H13.
            destruct H13. assert(ttqa M2 a <= sq a). apply H0.
            auto. lia. 
            all:auto. move /eqP in Haa'. auto.
          }
        }
      }
    (*Case when a' is more competitive ask than a *)
    { assert(ttqa M2 a' = 0\/ttqa M2 a' <>0) by eauto.
      destruct H9.  (*Case when more competitive does not belongs to M1*)
        { destruct (a_eqb a a') eqn:Haa'. move /eqP in Haa'. subst. lia.
          assert(HqaM2: ttqa M2 a>0). lia. assert(HM2A:In a (asks_of M2)). 
          { apply ttqa_intro1. lia. }
          assert(HA:In a A). apply H0 in HM2A. auto. 
          assert(HqaM1: ttqa M1 a'>0). lia. assert(HM1A:In a' (asks_of M1)). 
          { apply ttqa_intro1. lia. }
          assert(HA2:In a' A). apply H in  HM1A. auto.
          apply H3 in H8. destruct H8. specialize (NZA a'). 
          apply NZA in  HA2. lia. auto. move /eqP in Haa'.  auto. 
          auto. lia. 
        } (*Case when more competitive belongs to M2*)
        { assert(ttqa M2 a = 0\/ttqa M2 a <>0) by eauto.
          destruct H10.
          { lia. }
          { destruct (a_eqb a a') eqn:Haa'. move /eqP in Haa'. subst. lia.
            assert(HqaM1: ttqa M2 a>0). lia. assert(HM2A:In a (asks_of M2)). 
            { apply ttqa_intro1. lia. }
            assert(HA:In a A). apply H0 in HM2A. auto. 
            assert(HqaM2: ttqa M1 a'>0). lia. assert(HM1A:In a' (asks_of M1)). 
            { apply ttqa_intro1. lia. }
            assert(HA2:In a' A). apply H in  HM1A. auto.
            apply H3 with (s:=a')(s':=a) in H8 as H12. destruct H12.
            assert(ttqa M1 a' <= sq a'). apply H.
            auto. lia. 
            all:auto. move /eqP in Haa'. auto.
          }
        }
      }
    } Qed.




Lemma less_Q_implies_less_qb (M1 M2: list fill_type)(B:list Bid):
QMb M1 B < QMb M2 B ->
exists b' : Bid, (In b' B)/\(ttqb M1 b' < ttqb M2 b').
Proof. revert M1 M2. induction B as [|b B']. intros. simpl in H.
lia. intros. simpl in H. 
assert(Hb:(ttqb M1 b < ttqb M2 b)\/(ttqb M1 b >= ttqb M2 b)).
lia. destruct Hb. exists b. auto. assert(QMb M1 B' < QMb M2 B').
lia. apply IHB' in H1. destruct H1. destruct H1. exists x. auto. Qed.

Lemma size_equal_and_gt_imply_lt_bid (M1 M2: list fill_type)(B:list Bid)
(b:Bid):
(QMb M1 B = QMb M2 B) -> In b B -> (ttqb M1 b > ttqb M2 b) -> 
(exists b', (In b' B)/\(ttqb M1 b' < ttqb M2 b')).

Proof. intros. 
       induction B as [|b0 B']. elim H0. 
       simpl in H0. destruct H0. subst b0.
       simpl in H. assert(HM:QMb M1 B' < QMb M2 B').
       lia. apply less_Q_implies_less_qb with (B:=B') in HM.
       destruct HM. destruct H0. exists x. auto.
       simpl in H.
       assert(Hb:(ttqb M1 b0 < ttqb M2 b0)
       \/(ttqb M1 b0 = ttqb M2 b0)
       \/(ttqb M1 b0 > ttqb M2 b0)).
       lia.
       destruct Hb.
       exists b0. auto.
       destruct H2.
       assert(QMb M1 B' = QMb M2 B').
       lia. apply IHB' in H3.
       destruct H3. destruct H3. exists x. auto.
       auto.
       assert(QMb M1 B' < QMb M2 B'). lia.
       apply less_Q_implies_less_qb with (B:=B') in H3.
       destruct H3. destruct H3. exists x. auto. Qed.
        



Lemma Qsize_equal_and_gt_imply_lt_bid (M1 M2: list fill_type)(B:list Bid)
(NDB: NoDup B)(b:Bid):
(QM(M1) = QM(M2)) -> (ttqb M1 b > ttqb M2 b) -> bids_of M1 [<=] B
-> bids_of M2 [<=] B ->
(exists b', (In b' B)/\(ttqb M1 b' < ttqb M2 b')).
Proof. intros. apply QM_equal_QMb in H1 as H3. apply QM_equal_QMb in H2 as H4.
       rewrite <- H3 in H. rewrite <- H4 in H.
       assert(Hb1:In b (bids_of M1)). apply ttqb_intro1. lia.
       assert (Hb2: In b B). eauto.
       apply size_equal_and_gt_imply_lt_bid with (b:=b). all:auto. Qed. 
       


Theorem completeness_bids (M1 M2: list fill_type) (B:list Bid) (A:list Ask)
(NZB: forall b, In b B -> (bq b)>0)
(NZA: forall a, In a A -> (sq a)>0)
(NDB: NoDup B)(b:Bid):
  (matching_in B A M1)/\ (matching_in B A M2) 
  /\(QM(M1) = QM(M2))
  /\(fair_on_bids M1 B) /\ (fair_on_bids M2 B)
    -> (ttqb M1 b = ttqb M2 b).
Proof. intros. destruct H. destruct H0. destruct H1. destruct H2. 
unfold fair_on_bids in H2. unfold fair_on_bids in H3.
assert(Htb:ttqb M1 b = ttqb M2 b\/ttqb M1 b <> ttqb M2 b).
eauto. destruct Htb. auto.
assert(Hgb:ttqb M1 b > ttqb M2 b\/ttqb M1 b < ttqb M2 b).
 lia. destruct Hgb. 
  (*Case when there exists a bid a such that it's total trade quantities is more in M1 than M2*)
  { assert(exists b', (In b' B)/\(ttqb M1 b' < ttqb M2 b')).
    {  
      apply Qsize_equal_and_gt_imply_lt_bid with (b:=b). all:auto.
      apply H. apply H0.
    }
    destruct H6 as [b' H6]. destruct H6.
    assert(Hb: (by_dbp b b')\/(by_dbp b' b)). apply by_dbp_P.
    destruct Hb. 
    (*Case when b is more competitive bid than b' *)
    { assert(ttqb M2 b = 0\/ttqb M2 b <>0) by eauto.
      destruct H9.  (*Case when more competitive does not belongs to M2*)
        { destruct (b_eqb b b') eqn:Hbb'. move /eqP in Hbb'. subst. lia.
          assert(HqbM1: ttqb M1 b>0). lia. assert(HM1B:In b (bids_of M1)). 
          { apply ttqb_intro1. lia. }
          assert(HB:In b B). apply H in  HM1B. auto. 
          assert(HqbM2: ttqb M2 b'>0). lia. assert(HM2B:In b' (bids_of M2)). 
          { apply ttqb_intro1. lia. }
          assert(HB2:In b' B). apply H0 in  HM2B. auto.
          apply H3 in H8. destruct H8. specialize (NZB b). 
          apply NZB in HB. lia. auto. move /eqP in Hbb'.  auto. 
          auto. lia. 
        } (*Case when more competitive belongs to M2*)
        { assert(ttqb M1 b = 0\/ttqb M1 b <>0) by eauto.
          destruct H10.
          { lia. }
          { destruct (b_eqb b b') eqn:Hbb'. move /eqP in Hbb'. subst. lia.
            assert(HqbM1: ttqb M1 b>0). lia. assert(HM1B:In b (bids_of M1)). 
            { apply ttqb_intro1. lia. }
            assert(HB:In b B). apply H in  HM1B. auto. 
            assert(HqbM2: ttqb M2 b'>0). lia. assert(HM2B:In b' (bids_of M2)). 
            { apply ttqb_intro1. lia. }
            assert(HB2:In b' B). apply H0 in  HM2B. auto.
            assert(ttqb M2 b' >0) by lia. 
            apply H3 with (b:=b)(b':=b') in H11 as H13.
            destruct H13. assert(ttqb M1 b <= bq b). apply H.
            auto. lia. 
            all:auto. move /eqP in Hbb'. auto.
          }
        }
      }
    (*Case when b' is more competitive bid than b *)
    { assert(ttqb M1 b' = 0\/ttqb M1 b' <>0) by eauto.
      destruct H9.  (*Case when more competitive does not belongs to M1*)
        { destruct (b_eqb b b') eqn:Hbb'. move /eqP in Hbb'. subst. lia.
          assert(HqbM1: ttqb M2 b'>0). lia. assert(HM2B:In b' (bids_of M2)). 
          { apply ttqb_intro1. lia. }
          assert(HB:In b' B). apply H0 in HM2B. auto. 
          assert(HqbM2: ttqb M1 b>0). lia. assert(HM1B:In b (bids_of M1)). 
          { apply ttqb_intro1. lia. }
          assert(HB2:In b B). apply H in  HM1B. auto.
          apply H2 in H8. destruct H8. specialize (NZB b'). 
          apply NZB in  HB. lia. auto. move /eqP in Hbb'.  auto. 
          auto. lia. 
        } (*Case when more competitive belongs to M2*)
        { assert(ttqb M2 b' = 0\/ttqb M2 b' <>0) by eauto.
          destruct H10.
          { lia. }
          { destruct (b_eqb b b') eqn:Hbb'. move /eqP in Hbb'. subst. lia.
            assert(HqbM1: ttqb M2 b'>0). lia. assert(HM2B:In b' (bids_of M2)). 
            { apply ttqb_intro1. lia. }
            assert(HB:In b' B). apply H0 in HM2B. auto. 
            assert(HqbM2: ttqb M1 b>0). lia. assert(HM1B:In b (bids_of M1)). 
            { apply ttqb_intro1. lia. }
            assert(HB2:In b B). apply H in  HM1B. auto.
            apply H2 with (b:=b')(b':=b) in H8 as H12. destruct H12.
            assert(ttqb M2 b' <= bq b'). apply H0.
            auto. lia. 
            all:auto. move /eqP in Hbb'. auto.
          }
        }
      }
    }
      (*Case when there exists an ask a such that it's total trade quantities is more in M1 than M2*)
  { assert(exists b', (In b' B)/\(ttqb M1 b' > ttqb M2 b')).
    {  
      apply Qsize_equal_and_gt_imply_lt_bid with (b:=b). all:auto.
      apply H0. apply H.
    }
    destruct H6 as [b' H6]. destruct H6.
    assert(Hb: (by_dbp b b')\/(by_dbp b' b)). apply by_dbp_P.
    destruct Hb. 
    (*Case when b is more competitive bid than b' *)
    { assert(ttqb M1 b = 0\/ttqb M1 b <>0) by eauto.
      destruct H9.  (*Case when more competitive does not belongs to M2*)
        { destruct (b_eqb b b') eqn:Hbb'. move /eqP in Hbb'. subst. lia.
          assert(HqbM2: ttqb M2 b>0). lia. assert(HM2B:In b (bids_of M2)). 
          { apply ttqb_intro1. lia. }
          assert(HB:In b B). apply H0 in  HM2B. auto. 
          assert(HqbM1: ttqb M1 b'>0). lia. assert(HM1B:In b' (bids_of M1)). 
          { apply ttqb_intro1. lia. }
          assert(HB2:In b' B). apply H0 in HM2B. auto.
          eapply H2 with (b:=b) in HqbM1. destruct HqbM1. specialize (NZB b). 
          apply NZB in  HB. lia. auto. move /eqP in Hbb'.  auto. 
          auto. auto. 
        } (*Case when more competitive belongs to M2*)
        { assert(ttqb M2 b = 0\/ttqb M2 b <>0) by eauto.
          destruct H10.
          { lia. }
          { destruct (b_eqb b b') eqn:Hbb'. move /eqP in Hbb'. subst. lia.
            assert(HqbM2: ttqb M2 b>0). lia. assert(HM2B:In b (bids_of M2)). 
            { apply ttqb_intro1. lia. }
            assert(HB:In b B). apply H0 in  HM2B. auto. 
            assert(HqbM1: ttqb M1 b'>0). lia. assert(HM1B:In b' (bids_of M1)). 
            { apply ttqb_intro1. lia. }
            assert(HB2:In b' B). apply H0 in HM2B. auto.
            apply H2 with (b:=b)(b':=b') in HqbM1 as H13.
            destruct H13. assert(ttqb M2 b <= bq b). apply H0.
            auto. lia. 
            all:auto. move /eqP in Hbb'. auto.
          }
        }
      }
    (*Case when b' is more competitive bid than b *)
    { assert(ttqb M2 b' = 0\/ttqb M2 b' <>0) by eauto.
      destruct H9.  (*Case when more competitive does not belongs to M1*)
        { destruct (b_eqb b b') eqn:Hbb'. move /eqP in Hbb'. subst. lia.
          assert(HqbM2: ttqb M2 b>0). lia. assert(HM2B:In b (bids_of M2)). 
          { apply ttqb_intro1. lia. }
          assert(HB:In b B). apply H0 in HM2B. auto. 
          assert(HqbM1: ttqb M1 b'>0). lia. assert(HM1B:In b' (bids_of M1)). 
          { apply ttqb_intro1. lia. }
          assert(HB2:In b' B). apply H in  HM1B. auto.
          apply H3 in H8. destruct H8. specialize (NZB b'). 
          apply NZB in  HB2. lia. auto. move /eqP in Hbb'.  auto. 
          auto. lia. 
        } (*Case when more competitive belongs to M2*)
        { assert(ttqb M2 b = 0\/ttqb M2 b <>0) by eauto.
          destruct H10.
          { lia. }
          { destruct (b_eqb b b') eqn:Hbb'. move /eqP in Hbb'. subst. lia.
            assert(HqbM1: ttqb M2 b>0). lia. assert(HM2B:In b (bids_of M2)). 
            { apply ttqb_intro1. lia. }
            assert(HB:In b B). apply H0 in HM2B. auto. 
            assert(HqbM2: ttqb M1 b'>0). lia. assert(HM1B:In b' (bids_of M1)). 
            { apply ttqb_intro1. lia. }
            assert(HB2:In b' B). apply H in  HM1B. auto.
            apply H3 with (b:=b')(b':=b) in H8 as H12. destruct H12.
            assert(ttqb M1 b' <= bq b'). apply H.
            auto. lia. 
            all:auto. move /eqP in Hbb'. auto.
          }
        }
      }
    } Qed.


Theorem completeness (M1 M2: list fill_type) (B:list Bid) (A:list Ask)
(NZB: forall b, In b B -> (bq b)>0)
(NZA: forall a, In a A -> (sq a)>0)
(NDB: NoDup B)(NDA: NoDup A)
(b:Bid) (a:Ask):
(matching_in B A M1)/\ (matching_in B A M2) /\(QM(M1) = QM(M2))
/\(Is_fair M1 B A) /\ (Is_fair M2 B A)
-> (ttqa M1 a = ttqa M2 a)/\(ttqb M1 b = ttqb M2 b).
Proof. intros. split.
                { apply completeness_asks with (B:=B)(A:=A). all:auto. 
                  split. apply H. split. apply H. split. apply H. split. apply H. apply H.
                }
                { apply completeness_bids with (B:=B)(A:=A). all:auto. 
                  split. apply H. split. apply H. split. apply H. split. apply H. apply H.
                } Qed.



Lemma soundness_asks (M1 M2: list fill_type) (B:list Bid) (A:list Ask)
(NZB: forall b, In b B -> (bq b)>0)
(NZA: forall a, In a A -> (sq a)>0)
(NDA: NoDup A):
(matching_in B A M1)-> (matching_in B A M2) ->(forall a, (ttqa M1 a = ttqa M2 a))
->(fair_on_asks M1 A)  
-> (fair_on_asks M2 A).
Proof. unfold fair_on_asks. intros. specialize (H1 s') as Hs'.  specialize (H1 s) as Hs. 
                  assert(ttqa M1 s' > 0). lia. 
                  eapply H2 with (s:=s)(s':=s') in H8. destruct H8. 
                  assert(In s A). apply H. auto. assert(In s' A). apply H0. auto. 
                  specialize (NZA s). apply NZA in H10. assert(ttqa M2 s = sq s). lia. split.
                  eapply ttqa_intro1.  lia. all: auto. apply ttqa_intro1. lia. Qed.

Lemma soundness_bids (M1 M2: list fill_type) (B:list Bid) (A:list Ask)
(NZB: forall b, In b B -> (bq b)>0)
(NZA: forall a, In a A -> (sq a)>0)
(NDA: NoDup B):
(matching_in B A M1)-> (matching_in B A M2) ->(forall b, (ttqb M1 b = ttqb M2 b))
->(fair_on_bids M1 B)  
-> (fair_on_bids M2 B).
Proof. unfold fair_on_bids. intros. specialize (H1 b') as Hb'.  specialize (H1 b) as Hb. 
                  assert(ttqb M1 b' > 0). lia. 
                  eapply H2 with (b:=b)(b':=b') in H7. destruct H7. 
                  assert(In b B). apply H. auto. assert(In b' B). apply H0. auto. 
                  specialize (NZB b). apply NZB in H9. assert(ttqb M2 b = bq b). lia. split.
                  eapply ttqb_intro1.  lia. all: auto. apply ttqb_intro1. lia. Qed.


Theorem soundness (M1 M2: list fill_type) (B:list Bid) (A:list Ask)
(NZB: forall b, In b B -> (bq b)>0)
(NZA: forall a, In a A -> (sq a)>0)
(NDB: NoDup B)(NDA: NoDup A):
(matching_in B A M1)-> (matching_in B A M2) ->
(forall b, (ttqb M1 b = ttqb M2 b))/\(forall a, (ttqa M1 a = ttqa M2 a))
->(Is_fair M1 B A)  
-> (Is_fair M2 B A).
Proof. intros. destruct H2. split.
                { apply soundness_asks with (B:=B)(A:=A)(M2:=M2) in H2. all:auto. apply H1. 
                }
                { apply soundness_bids with (B:=B)(A:=A)(M2:=M2) in H3. all:auto. apply H1. 
                } Qed.

End Uniqueness.