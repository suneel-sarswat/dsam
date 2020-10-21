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
Require Export mFair_Ask.
Require Export MQFair.
Require Export MatchingAlter.
Require Export mUM.


Section MM.

Equations MM_aux (B:list Bid) (A: list Ask) (tb ta: nat): 
(list fill_type) by wf (|B| + |A|):=
MM_aux nil _ _ _:= nil;
MM_aux _ nil _ _:= nil;
MM_aux (b::B') (a::A') tb ta :=  
if (Nat.leb a b) then 
(
 if (Nat.eqb (bq b - tb) (sq a - ta) ) then
  ((Mk_fill b a (bq b - tb) (bp b))::(MM_aux B' A' 0 0))
 else 
  (if (Nat.leb (bq b - tb) (sq a - ta) ) then
    (Mk_fill b a (bq b - tb) (bp b))::(MM_aux B' (a::A') 0 (ta + (bq b - tb))) 
     else
    (Mk_fill b a (sq a - ta) (bp b))::(MM_aux (b::B') A' (tb + (sq a - ta)) 0)  
  )
) else (MM_aux (b::B') A' tb ta). 

Next Obligation.
lia. Qed.
Next Obligation.
lia. Qed.
Next Obligation.
lia. Qed.



Definition by_dsp (s1:Ask) (s2:Ask) := (Nat.leb s2 s1) ||
((Nat.eqb s2 s1) && (Nat.leb (stime s2)  (stime s1) )).

Lemma by_dsp_P : transitive by_dsp /\ comparable by_dsp.
Proof.  Proof.  { split.
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
          { unfold comparable. unfold by_dsp. intros. move /orP in H.
            assert (~ ((Nat.leb y x))). eauto. 
            unfold not in H0. apply /orP. left. 
            destruct x. destruct y. simpl in H0.
            apply comp_triv. auto. } } Qed.

Lemma by_dsp_refl: reflexive by_dsp.
Proof. unfold reflexive. intros. unfold by_dsp. apply /orP. 
left. apply nat_reflexive.  Qed.


Hint Resolve by_dsp_P by_dsp_refl: core.


Lemma MM_aux_subset_bidsB (B: list Bid) (A: list Ask) (tb ta:nat):
  (bids_of (MM_aux B A tb ta)) [<=] B.
  Proof. funelim (MM_aux B A tb ta).
  simp UM_aux. auto. simp UM_aux. auto.
  rewrite <- Heqcall. 
  destruct (Nat.leb a b) eqn: Hab.
  { destruct (Nat.eqb (bq b - tb) (sq a - ta)) eqn: Heq.
    { simpl. eapply Subset_intro. auto. }
    { destruct (Nat.leb (bq b - tb) (sq a - ta)) eqn: Hle.
      { simpl. eapply Subset_intro. auto. }
      { simpl. apply subset_elim1. auto. }
    }
  }
  auto.
 Qed. 


Lemma MM_aux_subset_asksA (B: list Bid) (A: list Ask) (tb ta:nat):
  (asks_of (MM_aux B A tb ta)) [<=] A.
  Proof. funelim (MM_aux B A tb ta).
  simp MM_aux. auto. simp MM_aux. auto. 
  rewrite <- Heqcall.
  destruct (Nat.leb a b) eqn: Hab.
  { destruct (Nat.eqb (bq b - tb) (sq a - ta)) eqn: Heq.
    { simpl. eapply Subset_intro. auto. }
    { destruct (Nat.leb (bq b - tb) (sq a - ta)) eqn: Hle.
      { simpl. apply subset_elim1. auto. }
      { simpl. eapply Subset_intro. auto. }      
    }
  }
  auto.
 Qed.

 


Theorem MM_aux_is_Ind_Rat (B: list Bid) (A:list Ask)(tb ta:nat):
  Sorted by_dbp B -> Sorted by_dsp A -> Is_IR (MM_aux B A tb ta).
Proof. {  unfold Is_IR. intros. unfold rational.
          funelim (MM_aux B A tb ta).
          simp MM_aux in H1. elim H1. 
          simp MM_aux in H1. elim H1. 
            destruct (Nat.leb a b) eqn: Hab.
            { move /leP in Hab. 
              destruct (Nat.eqb (bq b - tb) (sq a - ta)) eqn: Heq.
              { rewrite <- Heqcall in H5. simpl in H5.
                destruct H5. subst m. simpl. lia. 
                apply H in H5. auto.  eauto.  eauto. 
              } 
              { destruct (Nat.leb (bq b - tb) (sq a - ta)) eqn: Hle.
                { rewrite <- Heqcall in H5. simpl in H5.
                  destruct H5. subst m. simpl. lia. 
                  apply H0 in H5. auto.  eauto.  eauto.
                } 
                { rewrite <- Heqcall in H5. simpl in H5.
                  destruct H5. subst m. simpl. lia. 
                  apply H1 in H5. auto.  eauto.  eauto.
                }
              }
            }
            { rewrite <- Heqcall in H5. apply H2 in H5.
              auto.  eauto.  eauto.
            }
         }
Qed.


Lemma MM_aux_ttqb_b_le (B:list Bid) (A:list Ask)(tb ta:nat)(b:Bid)
(NDB: NoDup ((b::B)))(NDA: NoDup (A)):
ttqb (MM_aux (b::B) A tb ta) b <= bq b - tb.
Proof. funelim (MM_aux (b::B) A tb ta). 
  simp MM_aux. simpl. lia.
  simp MM_aux. 
  destruct (Nat.leb a b) eqn: Hab.
  { destruct (Nat.eqb (bq b - tb) (sq a - ta)) eqn: Heq.
    { simpl. destruct (b_eqb b b) eqn: Hbb. 
      cut(ttqb (MM_aux l l0 0 0) b= 0). lia.
      assert(~In b l).
      eauto. assert(~In b (bids_of (MM_aux l l0 0 0))).
      assert((bids_of (MM_aux l l0 0 0)) [<=] l).
      eapply MM_aux_subset_bidsB.
      eauto. apply ttqb_elim in H4. lia.
      move /eqP in Hbb. elim Hbb. auto.
    }
    { destruct (Nat.leb (bq b - tb) (sq a - ta)) eqn: Hle.
      { simpl. destruct (b_eqb b b) eqn: Hbb. 
        cut(ttqb (MM_aux l (a :: l0) 0 (ta + (bq b - tb))) b= 0). lia.
        assert(~In b l). 
        eauto. assert(~In b (bids_of 
        (MM_aux l (a :: l0) 0 (ta + (bq b - tb))))).
        assert((bids_of (MM_aux l (a :: l0) 0 (ta + (bq b - tb)))) [<=] l).
        eapply MM_aux_subset_bidsB.
        eauto. apply ttqb_elim in H4. lia.
        move /eqP in Hbb. elim Hbb. auto.
      }
      { simpl. destruct (b_eqb b b) eqn: Hbb. assert (NoDup (l0)).
        eauto. apply H1 in H3. move /leP in Hle. lia. eauto.
        move /eqP in Hbb. elim Hbb. auto.
      }
  }
}
apply H2. auto. eauto. 
Qed.

Lemma MM_aux_ttqb_b0 (B:list Bid) (A:list Ask)(tb ta:nat)(b b0:Bid)
(NDB: NoDup ((b::B)))(NDA: NoDup (A)):
b0<>b ->
ttqb (MM_aux (b::B) A tb ta) b0 <= bq b0.
Proof. funelim (MM_aux (b::B) A tb ta). 
  simp MM_aux. simpl. intros. lia.
  simp MM_aux. intros. simpl. destruct (b_eqb b1 b) eqn: Hb1b.
  move /eqP in Hb1b. subst b1. elim H3. auto.
  destruct (Nat.leb a b) eqn: Hab.
  { destruct (Nat.eqb (bq b - tb) (sq a - ta)) eqn: Heq.
    { simpl. rewrite Hb1b. destruct l. simp MM_aux. 
      simpl. lia. 
      destruct (b_eqb b1 b0) eqn:Hb1b0. move /eqP in Hb1b0.
      subst b0. replace (bq b1) with (bq b1 - 0). 
      eapply MM_aux_ttqb_b_le with (b:=b1)(tb:=0). eauto.
      eauto. lia.  move /eqP in Hb1b0. eapply H in Hb1b0. eauto.
      eauto. eauto. auto. auto.
    }
    { destruct (Nat.leb (bq b - tb) (sq a - ta)) eqn: Hle.
      { simpl. rewrite Hb1b. destruct l. simp MM_aux. 
        simpl. lia. 
        destruct (b_eqb b1 b0) eqn:Hb1b0. move /eqP in Hb1b0.
        subst b0. replace (bq b1) with (bq b1 - 0). 
        eapply MM_aux_ttqb_b_le with (b:=b1)(tb:=0). eauto.
        eauto. lia.  move /eqP in Hb1b0. eapply H0 in Hb1b0. eauto.
        eauto. eauto. auto. auto.
      }
      { simpl. rewrite Hb1b. move /eqP in Hb1b. eapply H1 in Hb1b. auto.
        eauto. eauto.
    }
  }
}
eapply H2.  eauto. eauto. auto.
Qed.

Lemma MM_aux_ttqb (B:list Bid) (A:list Ask)(b:Bid)
(NDB: NoDup (B))(NDA: NoDup (A)):
ttqb (MM_aux B A 0 0) b <= bq b.
Proof. destruct B. simp MM_aux. simpl. lia.
       destruct (b_eqb b0 b) eqn: Hb. 
       move /eqP in Hb.
       subst. replace (bq b) with (bq b - 0).
       eapply MM_aux_ttqb_b_le with (tb:=0)(ta:=0)(A:=A)(B:=B)(b:=b).
       eauto. eauto. lia. 
       move /eqP in Hb.
       apply MM_aux_ttqb_b0. eauto. eauto. auto. Qed.

(*begin: ttqa*)


Lemma MM_aux_ttqa_a_le (B:list Bid) (A:list Ask)(tb ta:nat)(a:Ask)
(NDB: NoDup ((B)))(NDA: NoDup ((a::A))):
ttqa (MM_aux (B) (a::A) tb ta) a <= sq a - ta.
Proof. funelim (MM_aux (B) (a::A) tb ta). 
  simp MM_aux. simpl. lia.
  simp MM_aux. 
  destruct (Nat.leb a b) eqn: Hab.
  { destruct (Nat.eqb (bq b - tb) (sq a - ta)) eqn: Heq.
    { simpl. destruct (a_eqb a a) eqn: Haa. 
      cut(ttqa (MM_aux l l0 0 0) a= 0). 
      move /eqP in Heq. lia.
      assert(~In a l0). 
      eauto. assert(~In a (asks_of (MM_aux l l0 0 0))).
      assert((asks_of (MM_aux l l0 0 0)) [<=] l0).
      eapply MM_aux_subset_asksA.
      eauto. apply ttqa_elim in H4. lia.
      move /eqP in Haa. elim Haa. auto.
    }
    { destruct (Nat.leb (bq b - tb) (sq a - ta)) eqn: Hle.
      { simpl. destruct (a_eqb a a) eqn: Haa. assert (NoDup (l)).
        eauto. apply H0 in H3. move /leP in Hle. lia. eauto.
        move /eqP in Haa. elim Haa. auto.
      }
      { simpl. destruct (a_eqb a a) eqn: Haa. 
        cut(ttqa (MM_aux (b :: l) l0 (tb + (sq a - ta)) 0) a= 0). 
        move /eqP in Heq. lia.
        assert(~In a l0).
        eauto. 
        assert(~In a (asks_of (MM_aux (b :: l) l0 (tb + (sq a - ta)) 0))).
        assert(asks_of (MM_aux (b :: l) l0 (tb + (sq a - ta)) 0) [<=] l0).
        eapply MM_aux_subset_asksA.
        eauto. apply ttqa_elim in H4. lia.
        move /eqP in Haa. elim Haa. auto.
      }
    }
  }
assert(~In a (asks_of (MM_aux (b :: l) l0 tb ta))).
assert((asks_of (MM_aux (b :: l) l0 tb ta))[<=]l0).
eapply MM_aux_subset_asksA. 
assert(~In a l0). 
eauto. eauto. 
apply ttqa_elim in H3. lia.
Qed.

Lemma MM_aux_ttqa_a0 (B:list Bid) (A:list Ask)(tb ta:nat)(a a0:Ask)
(NDB: NoDup ((B)))(NDA: NoDup ((a::A))):
a0<>a ->
ttqa (MM_aux (B) (a::A) tb ta) a0 <= sq a0.
Proof. funelim (MM_aux (B) (a::A) tb ta). 
  simp MM_aux. simpl. intros. lia.
  simp MM_aux. intros. simpl. destruct (a_eqb a1 a) eqn: Ha1a.
  move /eqP in Ha1a. subst a1. elim H3. auto.
  destruct (Nat.leb a b) eqn: Hab.
  { destruct (Nat.eqb (bq b - tb) (sq a - ta)) eqn: Heq.
    { simpl. rewrite Ha1a. destruct l0. 
      destruct l. simp MM_aux. simpl. lia. simp MM_aux. simpl. lia.
      destruct (a_eqb a1 a0) eqn:Ha1a0. move /eqP in Ha1a0.
      subst a0. replace (sq a1) with (sq a1 - 0). 
      eapply MM_aux_ttqa_a_le with (a:=a1)(ta:=0). eauto.
      eauto. lia.  move /eqP in Ha1a0. eapply H in Ha1a0. eauto.
      eauto. eauto. auto. auto.
    }
    { destruct (Nat.leb (bq b - tb) (sq a - ta)) eqn: Hle.
      { simpl. rewrite Ha1a. move /eqP in Ha1a. eapply H0 in Ha1a. auto.
        eauto. eauto.
      }
      { simpl. rewrite Ha1a. destruct l0. simp MM_aux. 
        simpl. lia. 
        destruct (a_eqb a1 a0) eqn:Ha1a0. move /eqP in Ha1a0.
        subst a0. replace (sq a1) with (sq a1 - 0). 
        eapply MM_aux_ttqa_a_le with (a:=a1)(ta:=0). eauto.
        eauto. lia.  move /eqP in Ha1a0. eapply H1 in Ha1a0. eauto.
        eauto. eauto. auto. auto.
      }
  }
}
destruct l0. simp MM_aux.  simpl. lia.
destruct (a_eqb a1 a0) eqn:Ha1a0. move /eqP in Ha1a0.
subst a0. 
assert(ttqa (MM_aux (b :: l) (a1 :: l0) tb ta) a1 <= sq a1 - ta).
eapply MM_aux_ttqa_a_le with (a:=a1)(ta:=ta). eauto.
eauto. lia.  move /eqP in Ha1a0. eapply H2 in Ha1a0. eauto.
eauto. eauto. auto. auto.
Qed.



Lemma MM_aux_ttqa (B:list Bid) (A:list Ask)(a:Ask)
(NDB: NoDup (B))(NDA: NoDup (A)):
ttqa (MM_aux B A 0 0) a <= sq a.
Proof. destruct A. destruct B. simp MM_aux. simpl. lia. 
       simp MM_aux. simpl. lia. 
       destruct (a_eqb a0 a) eqn: Ha. 
       move /eqP in Ha.
       subst. replace (sq a) with (sq a - 0).
       eapply MM_aux_ttqa_a_le with (tb:=0)(ta:=0)(A:=A)(B:=B)(a:=a).
       eauto. eauto. lia. 
       move /eqP in Ha.
       apply MM_aux_ttqa_a0. eauto. eauto. auto. Qed.


Definition MM (B:list Bid)(A:list Ask):=
MM_aux (sort by_dbp B) (sort by_dsp (A)) 0 0.

Theorem MM_Is_Matching (B:list Bid)(A:list Ask)
(NDB: NoDup (B))(NDA: NoDup (A)):
matching_in B A (MM B A).
Proof. intros. split. 
               { split.
                 { unfold MM. unfold All_matchable.
                        intros.
                        eapply MM_aux_is_Ind_Rat with 
                        (A:=(sort by_dsp A))(B:=(sort by_dbp B)) in H.
                        unfold rational in H. lia. 
                        apply sort_correct. apply by_dbp_P.
                        apply by_dbp_P.
                        apply sort_correct. apply by_dsp_P.
                        apply by_dsp_P.
                 }
                 { split.
                   { intros. unfold MM.
                        eapply MM_aux_ttqb with 
                        (A:=(sort by_dsp A))(B:=(sort by_dbp B)).
                        eapply nodup_sort.  auto.
                        eapply nodup_sort.  auto.
                   }
                   { intros. 
                     apply MM_aux_ttqa. auto. auto. 
                   } 
                }
              }
              { split.
                unfold MM.
                assert(perm B (sort by_dbp B)).
                eauto.
                assert(bids_of (MM_aux (sort by_dbp B) (sort by_dsp A) 0 0)
                [<=] (sort by_dbp B)).
                apply MM_aux_subset_bidsB with 
                (A:=(sort by_dsp A))(B:=(sort by_dbp B)).
                eauto.
                assert(perm A (sort by_dsp A)).
                eauto. unfold MM.
                assert(asks_of (MM_aux (sort by_dbp B) (sort by_dsp A) 0 0)
                [<=] (sort by_dsp A)).
                apply MM_aux_subset_asksA with 
                (A:=(sort by_dsp A))(B:=(sort by_dbp B)).
                eauto.
              }
Qed.


(*Move this lemma into another file*)
Lemma exists_ttq_top_bid 
(B:list Bid)(A:list Ask)(M:list fill_type)(b:Bid)(q:nat):
Sorted by_dbp (b::B) -> 
(matching_in (b::B) (A) M) -> 
Is_IR M ->
QM(M)>=q-> 
bq b >= q -> (*Fix this issue*)
(exists M', (matching_in (b::B) (A) M')/\
(ttqb M' b >= q)/\Is_IR M'/\ QM(M)=QM(M')).
Proof.   intros.
         set (M':=(FOB M (b::B))).
         assert (matching_in (b :: B) (A) M'). 
         (*proved property of FOA and FOB*)admit.
         assert (Is_IR M').
         (*TODO: property of FOA and FOB*)admit.
         assert (QM M' = QM M).
         (*proved property of FOA and FOB*)admit.
         exists M'. all:split;auto. split. 
         admit. split. auto. admit. Admitted.



Lemma MM_exists_opt_k (B:list Bid)(A:list Ask)(b:Bid)(a:Ask):
(*(NZT:forall m : fill_type, In m M -> tq m > 0)*)
Sorted by_dbp (b::B) -> 
Sorted by_dsp (a::A) -> 
(forall k M,
matching_in (b::B) (a::A) M -> 
b>=a ->
QM(M)>=(min (bq b) (sq a)) ->
(ttqb M b >= min (bq b) (sq a)) ->
min (bq b) (sq a) - ttq_ab M b a = k ->
(forall m : fill_type, In m M -> tq m > 0) ->
Is_IR M ->
(exists OPT, (matching_in (b::B) (a::A) OPT)/\
(min (bq b) (sq a) - ttq_ab OPT b a = 0)/\Is_IR OPT/\QM(M)=QM(OPT))).
Proof. intros B0 A0 k.
       case (Nat.leb (bq b) (sq a)) eqn:Hab.
       { 
         assert (min (bq b) (sq a) = bq b). 
         eapply min_l. move /leP in Hab;lia. rewrite H. 
         induction k.
         { intros M H0 H2 H3 H4 H5b NZT IR.  (*Base induction case*)
           assert (H6:ttq_ab M b a = bq b).
           assert(ttq_ab M b a <= bq b).
           apply matching_in_elim9b with (B:=b::B)(A:=a::A) .
           apply H0. lia.
           exists M. split;split.
           { eapply H0. }
           { split. 
              { 
               eapply H0. 
              }
              { eapply H0. 
              }
           }
           { auto. }
           { split. auto. lia. } 
         }
         { intros M H0 H1 H2 H3 H4 NZT IR.  (*Main induction case*)
           assert(ttq_ab M b a < bq b). lia.
           assert(ttqb M b = (bq b)). 
           assert(HMb : ttqb M b <= bq b). 
           assert(In b (bids_of M) \/~In b (bids_of M)).
           eauto. destruct H6. 
           eapply H0. auto. apply ttqb_elim in H6. lia. lia.
           assert(exists m1, (In m1 M/\ (bid_of m1) = b /\(ask_of m1) <>a )).
           eapply b_in_a_out_m_exists with (M:=M)(a:=a)(b:=b). eauto. lia.
           destruct (Nat.eqb (ttqa M a) (sq a)) eqn:Haq.
           (*There will be two cases, either a is traded at least (bq b) amount
           or not. In the first case we do the same surgery al old. In the
           second case we do new surgery.*)
           { assert(exists m2, (In m2 M/\ (ask_of m2) = a /\(bid_of m2) <>b )).
             eapply a_in_b_out_m_exists with (M:=M)(a:=a)(b:=b).
             move /eqP in Haq. lia. lia. 
             destruct H7 as [m1 H7]. destruct H8 as [m2 H8].
             assert(Hm1m2:m1<>m2).
             destruct H8. destruct H9.
             destruct H7. destruct H11. 
             assert(Hm1m2:m1 = m2 \/ m1 <> m2).
             eauto. destruct Hm1m2. subst m1. subst b. 
             elim H10.  auto. auto. 
             set (M':=(g_increase_top M m1 m2 b a)).
             assert(HM'size: QM M = QM M').
             apply g_increase_top_size. auto.
             apply H7. apply H8. 
             auto.
             assert(matching_in (b :: B) (a :: A) M'
             /\QM M' >= bq b /\ttqa M' a >= bq b/\ttqb M' b >= bq b
             /\bq b - ttq_ab M' b a = k/\Is_IR M'). split.
              { split. split. 
                { admit. (*write g_increase_top_matchable.*) }
                split. 
                { intros.
                  assert(ttqb M' b0 = ttqb M b0).  
                  eapply g_increase_top_ttqb. auto.
                  apply H8. apply H7. symmetry;apply H7.
                  symmetry;apply H8. auto. rewrite H10.
                  assert(In b0 (bids_of M)\/~In b0 (bids_of M)).
                  eauto. destruct H11. apply H0. auto.
                  apply ttqb_elim in H11. lia. 
                }
                { intros.
                  assert(ttqa M' a0 = ttqa M a0).  
                  eapply g_increase_top_ttqa. auto.
                  apply H8. apply H7. symmetry;apply H7.
                  symmetry;apply H8. auto. rewrite H10.
                  assert(In a0 (asks_of M)\/~In a0 (asks_of M)).
                  eauto. destruct H11. apply H0. auto.
                  apply ttqa_elim in H11. lia. 
                }
                split. 
                { assert(bids_of M' [<=]bids_of M). 
                  apply g_increase_top_bids_subset. 
                  apply H8. apply H7. symmetry;apply H7.
                  symmetry;apply H8. assert(bids_of M [<=] b :: B).
                  apply H0. eauto.
                }
                { assert(asks_of M' [<=]asks_of M). 
                  apply g_increase_top_asks_subset. 
                  apply H8. apply H7. symmetry;apply H7.
                  symmetry;apply H8. assert(asks_of M [<=] a :: A).
                  apply H0. eauto.
                }
              }
             split. lia. split. move /eqP in Haq.
             assert(ttqa M' a = ttqa M a).  
             eapply g_increase_top_ttqa. auto.
             apply H8. apply H7. symmetry;apply H7.
             symmetry;apply H8. auto. lia.
             split.
             assert(ttqb M' b = ttqb M b).  
             eapply g_increase_top_ttqb. auto.
             apply H8. apply H7. symmetry;apply H7.
             symmetry;apply H8. auto. lia. 
             rewrite g_increase_top_trade_equal. all:auto.
             apply H8. apply H7. symmetry;apply H8. 
             destruct H8. destruct H9. auto.
             symmetry;apply H7. 
             destruct H7. destruct H9. auto. 
             split. lia. admit.
             eapply IHk with (M:=M') in H1. destruct H1 as [OPT H1]. 
             destruct H1.  destruct H10. exists OPT. split. auto.
             split. auto. split. apply H11. lia. all: try apply H9. 
             apply g_increase_top_NZT. auto.
             apply H7. apply H8. 
          }
          { move /eqP in Haq. assert(ttqa M a < sq a).
            assert(ttqa M a <= sq a). 
            assert(In a (asks_of M)\/~In a (asks_of M)).
            eauto. destruct H8. apply H0. auto.
            apply ttqa_elim in H8. lia. 
            lia.
            (*apply surgery here with m1*) admit.
          }
        }
      }
      { (*Case -2 bq b >= sq*)
         
         assert (min (bq b) (sq a) = sq a).
         eapply min_r. move /leP in Hab;lia. rewrite H. 
         induction k.
         { intros M H0 H1 H2 H3 H4 NZT IR.  (*Base induction case*)
           assert (H6:ttq_ab M b a = sq a).
           assert(ttq_ab M b a <= sq a).
           apply matching_in_elim9a with (B:=b::B)(A:=a::A) .
           apply H0. lia.
           exists M. split;split.
           { eapply H0. }
           { split. 
              { 
               eapply H0. 
              }
              { eapply H0. 
              }
           }
           { auto. }
           { split. auto. lia. } 
         }
         { intros M H0 H1 H2 H3 H4 NZT IR.  (*Main induction case*)
           assert(exists m1, (In m1 M/\ (bid_of m1) = b /\(ask_of m1) <>a )).
           eapply b_in_a_out_m_exists with (M:=M)(a:=a)(b:=b). eauto. lia.
           destruct (Nat.eqb (ttqa M a) (sq a)) eqn:Haq.
           (*There will be two cases, either a is traded at least (bq b) amount
           or not. In the first case we do the same surgery al old. In the
           second case we do new surgery.*)
           { assert(exists m2, (In m2 M/\ (ask_of m2) = a /\(bid_of m2) <>b )).
             eapply a_in_b_out_m_exists with (M:=M)(a:=a)(b:=b).
             move /eqP in Haq. lia. lia. 
             destruct H5 as [m1 H5]. destruct H6 as [m2 H6].
             assert(Hm1m2:m1<>m2).
             assert(Hm1m2:m1 = m2 \/ m1 <> m2).
             eauto. destruct Hm1m2. subst m1.
             destruct H5. destruct H7. subst b. 
             destruct H6. destruct H7. subst a.
             elim H8.  auto. auto. 
             set (M':=(g_increase_top M m1 m2 b a)).
             assert(HM'size: QM M = QM M').
             apply g_increase_top_size. auto.
             apply H5. apply H6. 
             auto.
             assert(matching_in (b :: B) (a :: A) M'
             /\QM M' >= sq a /\ttqa M' a >= sq a/\ttqb M' b >= sq a
             /\sq a - ttq_ab M' b a = k/\ Is_IR M'). split.
              { split. split. 
                { admit. (*write g_increase_top_matchable.*) }
                split. 
                { intros.
                  assert(ttqb M' b0 = ttqb M b0).  
                  eapply g_increase_top_ttqb. auto.
                  apply H6. apply H5. symmetry;apply H5.
                  symmetry;apply H6. auto. rewrite H8.
                  assert(In b0 (bids_of M)\/~In b0 (bids_of M)).
                  eauto. destruct H9. apply H0. auto.
                  apply ttqb_elim in H9. lia. 
                }
                { intros.
                  assert(ttqa M' a0 = ttqa M a0).  
                  eapply g_increase_top_ttqa. auto.
                  apply H6. apply H5. symmetry;apply H5.
                  symmetry;apply H6. auto. rewrite H8.
                  assert(In a0 (asks_of M)\/~In a0 (asks_of M)).
                  eauto. destruct H9. apply H0. auto.
                  apply ttqa_elim in H9. lia. 
                }
                split. 
                { assert(bids_of M' [<=]bids_of M). 
                  apply g_increase_top_bids_subset. 
                  apply H6. apply H5. symmetry;apply H5.
                  symmetry;apply H6. assert(bids_of M [<=] b :: B).
                  apply H0. eauto.
                }
                { assert(asks_of M' [<=]asks_of M). 
                  apply g_increase_top_asks_subset. 
                  apply H6. apply H5. symmetry;apply H5.
                  symmetry;apply H6. assert(asks_of M [<=] a :: A).
                  apply H0. eauto.
                }
              }
             split. lia. split. move /eqP in Haq.
             assert(ttqa M' a = ttqa M a).  
             eapply g_increase_top_ttqa. auto.
             apply H6. apply H5. symmetry;apply H5.
             symmetry;apply H6. auto. lia.
             split.
             assert(ttqb M' b = ttqb M b).  
             eapply g_increase_top_ttqb. auto.
             apply H6. apply H5. symmetry;apply H5.
             symmetry;apply H6. auto. lia. 
             rewrite g_increase_top_trade_equal. all:auto.
             apply H6. apply H5. symmetry;apply H6. 
             destruct H6. destruct H7. auto.
             symmetry;apply H5. 
             destruct H5. destruct H7. auto. split. 
             lia. admit.
             eapply IHk with (M:=M') in H1. destruct H1 as [OPT H1]. 
             destruct H1.  destruct H8. exists OPT. split. auto.
             split. auto. split. apply H9. lia. all: try apply H7. 
             apply g_increase_top_NZT. auto.
             apply H5. apply H6. 
          }
          { move /eqP in Haq. assert(ttqa M a < sq a).
            assert(ttqa M a <= sq a). 
            assert(In a (asks_of M)\/~In a (asks_of M)).
            eauto. destruct H6. apply H0. auto.
            apply ttqa_elim in H6. lia. 
            lia.
            (*apply surgery here with m1*) admit.
          }
        }
      }
Admitted.

Lemma MM_exists_opt (B:list Bid)(A:list Ask)(M:list fill_type)(b:Bid)(a:Ask)
(NZT: forall m : fill_type, In m M -> tq m > 0):
Sorted by_dbp (b::B) -> 
Sorted by_dsp (a::A) -> 
(matching_in (b::B) (a::A) M) -> 
b>=a ->
QM(M)>=min (bq b) (sq a) ->
Is_IR M ->
(exists OPT, (matching_in (b::B) (a::A) OPT)/\
(ttq_ab OPT b a = min (bq b) (sq a))/\Is_IR OPT/\QM(M)=QM(OPT)).
Proof. intros. 
       assert((exists M', (matching_in (b::B) (a::A) M')/\
       (ttqb M' b >= bq b)/\(Is_IR M') /\QM(M)=QM(M'))).
       eapply exists_ttq_top_bid. all:auto. destruct H5 as [M0 H5].
       destruct H5. destruct H6. destruct H7. 
       destruct (Nat.min (bq b) (sq a) - ttq_ab M0 b a) eqn:Hk.
       {
         eapply MM_exists_opt_k with (k:=0)(A:=A)(a:=a)(B:=B)(b:=b) in H5.
         destruct H5 as [OPT H5]. exists OPT. 
         destruct H5. destruct H9.
         split. apply H5. split. 
         assert (Hmin:ttq_ab OPT b a <= Nat.min (bq b) (sq a)).
         eapply matching_in_elim9 with (B:=(b::B))(A:=(a::A)).
         apply H5.  lia. split. apply H10. lia. all:auto. lia. lia. admit.
       }  
       { assert(Haba:ttqa M0 a >=ttq_ab M0 b a).
         eauto. 
         eapply MM_exists_opt_k with (k:= S n)(A:=A)(a:=a)(B:=B)(b:=b) in H5.
         destruct H5 as [OPT H5]. exists OPT. 
         destruct H5. destruct H9.
         split. apply H5. split. 
         assert (Hmin:ttq_ab OPT b a <= Nat.min (bq b) (sq a)).
         eapply matching_in_elim9 with (B:=(b::B))(A:=(a::A)).
         apply H5.  lia. split. apply H10. lia. all:auto. lia. lia. admit.
       }
   Admitted. 


Theorem MM_aux_OPT (B:list Bid)(A:list Ask)(t:nat)(b:Bid)(a:Ask)(ta tb: nat)
(NDA:NoDup (idas_of A))(NDB:NoDup (idbs_of B)):
Sorted by_dbp (b::B) -> 
Sorted by_dsp (a::A) -> 
(forall M, matching_in ((Mk_bid (bp b) (btime b) (bq b - tb) (idb b))::B)
                        ((Mk_ask (sp a) (stime a) (sq a - ta) (ida a))::A) M
/\Is_IR M-> QM(M) <= QM(MM_aux (b::B) (a::A) tb ta)).
Proof. intros. 
assert(HBS: Sorted by_dbp ((Mk_bid (bp b) (btime b) (bq b - tb) (idb b))::B)).
constructor. eauto. intros. 
eapply Sorted_elim4 with (x0:=x) in H.
destruct b;destruct x. auto. auto.
assert(HAS: Sorted by_dsp ((Mk_ask (sp a) (stime a) (sq a - ta) (ida a))::A)).
constructor. eauto. intros. 
eapply Sorted_elim4 with (x0:=x) in H0.
destruct a;destruct x. auto. auto.
funelim (MM_aux (b::B) (a::A) tb ta).
rewrite <- Heqcall. 
destruct (Nat.leb a b) eqn: Hab.
{ 
  assert(Hab0: a <= b). move /leP in Hab. auto.
  destruct (Nat.leb (QM(M)) (min (bq b - tb) (sq a - ta))) eqn:Hqab.
  { 
    move /leP in Hqab.
    destruct (Nat.eqb (bq b - tb) (sq a - ta)). simpl. lia.
    destruct (Nat.leb (bq b - tb) (sq a - ta)) eqn:Hle.
    simpl. lia. simpl.
    move /eqP in Hle. lia.
  }
  {
    destruct H5 as [H5 IR]. eapply MM_exists_opt in H5.
    all:auto. 
    destruct H5 as [M0 H5].
    destruct H5. destruct H6. destruct H7. rewrite H8.
    destruct (Nat.eqb (bq b - tb) (sq a - ta)) eqn: Hqabeq.
    {
      simpl. simpl in H6.
      assert(HM0':exists M0', 
      (matching_in l l0 M0')/\Is_IR M0'/\(QM(M0)=QM(M0') + (bq b - tb))).
      {
        eapply exists_M0_reduced_bid_ask_matching in H5.
        destruct H5 as [M1 H5]. exists M1.
        destruct H5. simpl in H8. auto.
        (*NZT*)admit. simpl. split. rewrite H6.  
        move /eqP in Hqabeq. lia.
        move /eqP in Hqabeq. lia. auto.
      }
      destruct HM0' as [M0' HM0'].
      replace (QM M0) with (QM M0' + (bq b - tb)).
      cut(QM M0' <= QM (MM_aux l l0 0 0)). lia.
      case l eqn: Hl. simp MM_aux.
      simpl. (*Show that M0' is nil using HM0'*)admit.
      case l0 eqn: Hl0. simp MM_aux.
      simpl. (*Show that M0' is nil using HM0'*)admit.
      eapply H with (M:=M0'). all:auto.
      eauto. eauto. eauto. eauto.
      replace (bq b0 - 0) with (bq b0).
      replace (sq a0 - 0) with (sq a0).
      destruct HM0'. destruct b0;destruct a0.
      simpl. split. eapply H9. apply H10. auto. lia. lia.  
      replace (bq b0 - 0) with (bq b0).
      assert(Sorted by_dbp (b0 :: l1));eauto;destruct b0;auto.
      lia.
      replace (sq a0 - 0) with (sq a0).
      assert(Sorted by_dsp (a0 :: l2));eauto;destruct a0;auto.
      lia. destruct HM0';auto. destruct H10. lia.
    }
    {
      destruct (Nat.leb (bq b - tb) (sq a - ta)) eqn:Hle.
      {
        simpl. simpl in H6.
        case l eqn: Hl. simp MM_aux.
        simpl. 
        (*Show that in H4 size of M0 can't be more than  bq b - tb*)admit.
        assert(HM0':exists M0', (matching_in 
        ((Mk_bid (bp b0) (btime b0) (bq b0 - 0) (idb b0))::l1) 
        ((Mk_ask (sp a) (stime a) (sq a - (ta + (bq b - tb))) (ida a))::l0)
         M0')
        /\Is_IR M0'/\(QM(M0)=QM(M0') + (bq b - tb))).
        admit. destruct HM0' as [M0' HM0'].
        replace (QM M0) with (QM M0' + (bq b - tb)).
        cut(QM M0' <= QM (MM_aux (b0 :: l1) (a :: l0) 0 (ta + (bq b - tb)))).
        lia.
        eapply H0 with (M:=M0'). all:auto.
        eauto. eauto.
        destruct HM0'. 
        split. eapply H9. apply H10.
        replace (bq b0 - 0) with (bq b0). destruct b0;auto. eauto. 
        lia. 
        constructor. eauto. intros. simpl. 
        eapply Sorted_elim4 with (x0:=x) in H4.
        destruct a;destruct x. unfold by_sp. simpl.
        unfold by_dsp in H4. simpl in H4. auto. auto.
        destruct HM0'. destruct H10. auto. 
      }
      {
        simpl. simpl in H6.
        case l0 eqn: Hl0. simp MM_aux.
        simpl. 
        (*Show that in H4 size of M0 can't be more than sq a - ta*)admit.
        assert(HM0':exists M0', (matching_in 
        ((Mk_bid (bp b) (btime b) (bq b - (tb + (sq a - ta))) (idb b))::l)
        ((Mk_ask (sp a0) (stime a0) (sq a0 - 0) (ida a0))::l1) M0')
        /\Is_IR M0'/\(QM(M0)=QM(M0') + (sq a - ta))).
        { admit. (*
         eapply exists_M0_reduced_bid_uniform with (a:=
         {|
          sp := a;
          stime := stime a;
          sq := sq a - ta;
          ida := ida a |}) in H4.
         destruct H4 as [M1 H4]. exists M1.
         destruct H4. simpl in H4. 
         replace (bq b - (tb + (sq a - ta))) with (bq b - tb - (sq a - ta)).
         split. replace (sq a0 - 0) with (sq a0). 
         replace ({| sp := a0; stime := stime a0; sq := sq a0; ida := ida a0 |})
         with a0. eapply H4. destruct a0. simpl. auto.
         lia. simpl in H7. auto. lia. simpl. admit.
         admit. 
         simpl. rewrite H5.  
         move /leP in Hle. lia. 
         move /eqP in Hqabeq. move /leP in Hle. 
         simpl. lia.*)
        }
        destruct HM0' as [M0' HM0'].
        replace (QM M0) with (QM M0' + (sq a - ta)).
        cut(QM M0' <= QM (MM_aux (b :: l) (a0 :: l1) (tb + (sq a - ta)) 0)).
        lia.
        eapply H1 with (M:=M0'). all:auto.
        eauto. eauto.
        destruct HM0'. 
        split. eapply H9. apply H10.
        (*Prove Sorted property that reducing quantity does not changes sorted preperty*)
        constructor. eauto. intros. simpl. 
        eapply Sorted_elim4 with (x0:=x) in H3.
        destruct b;destruct x. unfold by_dsp. simpl.
        unfold by_dsp in H3. simpl in H3. auto. auto.
        replace (sq a0 - 0) with (sq a0). destruct a0;auto. eauto. 
        lia.
        destruct HM0'. destruct H10. auto.
        }
      }
      simpl. admit. simpl. move /leP in Hqab. lia. 
    }
  }
  admit. (*Need to reslve this case*)
Admitted.
End MM.



(**)
Print Uniform.
Print Is_uniform.
(*
Definition Is_MM (M : list fill_type)(B: list Bid)(A: list Ask) :=
  matching_in B A M /\ 
  (forall M': list fill_type, matching_in B A M' -> QM(M') <= QM(M)).
  
*)