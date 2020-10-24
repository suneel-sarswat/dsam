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
) else (MM_aux (b::B') A' tb 0). 

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
assert(~In a (asks_of (MM_aux (b :: l) l0 tb 0))).
assert((asks_of (MM_aux (b :: l) l0 tb 0))[<=]l0).
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
destruct (a_eqb a1 a0) eqn:Ha1a0.
move /eqP in Ha1a0.
subst a0. replace (sq a1) with (sq a1 - 0).
apply MM_aux_ttqa_a_le. all:auto. eauto. lia.
apply H2. all:auto. eauto.
move /eqP in Ha1a0. auto.
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
(B:list Bid)(A:list Ask)(M:list fill_type)(b:Bid)
(Hanti:antisymmetric by_dbp )(NDA:NoDup A)(NDB:NoDup (b::B))
(NZB:(forall b0, In b0 (b :: B) -> bq b0 > 0))
(NZT:forall m : fill_type, In m M -> tq m > 0):
Sorted by_dbp (b::B) -> 
(matching_in (b::B) (A) M) -> 
Is_IR M -> (*
QM(M)>=q-> 
bq b >= q -> (*Fix this issue*)*)
(exists M', (matching_in (b::B) (A) M')/\
(ttqb M' b >= min (bq b) (QM(M)))/\Is_IR M'/\ QM(M)=QM(M')/\
forall m : fill_type, In m M' -> tq m > 0).
Proof.   intros.
         set (M':=(FOB (sort m_dbp M) (sort by_dbp (b::B)))).
         assert (HM:matching_in (b :: B) (A) M').
         apply FOB_matching. all:auto.
         assert(Hq:QM((sort m_dbp M)) = QM(M)).
         eauto. 
         assert (Is_IR M').
         apply FOB_IR. all:auto.
         intros. eauto. apply sort_correct.
         apply by_dbp_P. apply by_dbp_P. apply sort_correct.
         apply m_dbp_P. apply m_dbp_P. intro.
         eauto. 
         assert(bids_of (sort m_dbp M) [<=]bids_of (M)).
         eauto. assert(bids_of M [<=] (b::B)).
         apply H0. eauto. 
         intro. assert(Ht:ttqb (sort m_dbp M) b0 = ttqb M b0).
         apply ttqb_of_perm. eauto. rewrite Ht.
         assert(Hb:In b0 (bids_of M)\/~In b0 (bids_of M)).
         eauto. destruct Hb as [Hb1 | Hb]. apply H0. auto.
         apply ttqb_elim in Hb. lia. 
         assert (HQ:QM M = QM M').
         rewrite <- Hq.
         apply FOB_size with (A:=A). all:auto.
         intros. eauto.
         apply match_inv with (B':=(sort by_dbp (b :: B)))
         (M':=(sort m_dbp M))(A':=A) in H0. auto.
         eauto. eauto. auto.
         assert(Htq:ttqb M' b = min (bq b) (QM(M))).
         assert(HB:(sort by_dbp (b::B))  = b::B).
         {
           apply sort_equal_nodup. apply by_dbp_refl. apply Hanti.
           all: auto.
         }
         subst M'. rewrite HB.
         assert(Hmin:Nat.min (bq b) (QM(M)) = (bq b)\/
         Nat.min (bq b) (QM(M)) = (QM(M))).
         lia. destruct Hmin as [Hmin1 | Hmin2].
         rewrite Hmin1.
         apply FOB_aux_top_bid_fair0 with (B:=B)(b:=b)
         (M:=(sort m_dbp M)). intros. eauto. auto.
         lia.
         rewrite Hmin2. rewrite <- Hq.
         apply FOB_ttqb_QM with (M:=(sort m_dbp M)).
         intros. eauto. auto. lia.
         exists M'.  split;auto. split. lia. split. auto.
         split.  auto. apply FOB_NZT. eauto. eauto.
         intros. eauto. Qed.


Lemma MM_exists_opt_k (B:list Bid)(A:list Ask)(b:Bid)(a:Ask):
(*(NZT:forall m : fill_type, In m M -> tq m > 0)*)
Sorted by_dbp (b::B) -> 
Sorted by_dsp (a::A) -> 
(forall k M,
matching_in (b::B) (a::A) M ->
Is_IR M -> 
b>=a ->
QM(M)>=(min (bq b) (sq a)) ->
(ttqb M b >= min (bq b) (sq a)) ->
min (bq b) (sq a) - ttq_ab M b a = k ->
(forall m : fill_type, In m M -> tq m > 0) ->
(exists OPT, (matching_in (b::B) (a::A) OPT)/\Is_IR OPT/\QM(M)=QM(OPT)/\
(min (bq b) (sq a) - ttq_ab OPT b a = 0)/\
forall m : fill_type, In m OPT -> tq m > 0)).
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
           { split. auto. split. lia. auto. } 
         }
         { intros M H0 IR H1 H2 H3 H4 NZT.  (*Main induction case*)
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
                { eapply g_increase_top_matchable.
                  all:auto. apply H8. apply H7. symmetry;apply H7.
                  symmetry;apply H8. 
                  {
                  apply Sorted_elim2 with (x:=(ask_of m1)) in A0.
                  unfold by_dsp in A0. move /orP in A0. destruct A0.
                  move /leP in H9. lia. move /andP in H9.
                  destruct H9. move /eqP in H9. lia.
                  apply by_dsp_refl. apply H0. destruct H7. eauto.
                  }
                  {
                  apply Sorted_elim2 with (x:=(bid_of m2)) in B0.
                  unfold by_dbp in A0. move /orP in B0. destruct B0.
                  move /leP in H9. lia. move /andP in H9.
                  destruct H9. move /eqP in H9. lia.
                  apply by_dbp_refl. apply H0. destruct H8. eauto.
                  }
                  apply H0. }
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
             split. lia. eapply g_increase_top_matching_IR.
             all:auto.
             
             apply H8. apply H7. symmetry;apply H7.
                  symmetry;apply H8. 
                  {
                  apply Sorted_elim2 with (x:=(ask_of m1)) in A0.
                  unfold by_dsp in A0. move /orP in A0. destruct A0.
                  move /leP in H9. lia. move /andP in H9.
                  destruct H9. move /eqP in H9. lia.
                  apply by_dsp_refl. apply H0. destruct H7. eauto.
                  }
                  {
                  apply Sorted_elim2 with (x:=(bid_of m2)) in B0.
                  unfold by_dbp in A0. move /orP in B0. destruct B0.
                  move /leP in H9. lia. move /andP in H9.
                  destruct H9. move /eqP in H9. lia.
                  apply by_dbp_refl. apply H0. destruct H8. eauto.
                  }
                  apply H0.
             eapply IHk with (M:=M') in H1. destruct H1 as [OPT H1]. 
             destruct H1.  destruct H10. exists OPT. split. auto.
             split. auto. split. rewrite HM'size.
             apply H11. split. lia. all: try apply H9. 
             apply H11.
             apply g_increase_top_NZT. auto.
             apply H7. apply H8. 
          }
          { move /eqP in Haq. assert(ttqa M a < sq a).
            assert(ttqa M a <= sq a). 
            assert(In a (asks_of M)\/~In a (asks_of M)).
            eauto. destruct H8. apply H0. auto.
            apply ttqa_elim in H8. lia. 
            lia.
            destruct H7 as [m H7].
            set (M':=increase_quantb_by_one M m b a).
            assert(Hmatch:matching_in (b::B) (a::A) M').
            { apply increase_quantb_by_one_matching.
              all:auto. apply H7. symmetry;apply H7.
              destruct H7. destruct H9. auto.
            }
            assert(HIR:Is_IR M').
            { apply increase_quantb_by_one_matching_IR.
              all:auto. apply H7. symmetry;apply H7.
              apply H0.
            }
            assert(HQ:QM(M)=QM(M')).
            { apply increase_quantb_by_one_size. all:auto.
              apply H7.
            }
            assert(Hqab:ttq_ab M' b a =1+ ttq_ab M b a).
            { apply increase_quantb_by_one_trade_correct.
              all:auto. apply H7. symmetry;apply H7.
              destruct H7. destruct H9. auto.
            }
            assert(HNZT:(forall m : fill_type, In m M' -> tq m > 0)).
            { apply increase_quantb_by_one_NZT. auto. apply H7. }
            assert(Hqb:ttqb M' b = ttqb M b).
            { apply increase_quantb_by_one_bqb_equal. all:auto.
              apply H7. symmetry;apply H7.
            }
            apply IHk with (M:=M') in Hmatch as HOPT.
            all:auto. destruct HOPT as [M1 HM1]. 
            destruct HM1 as [HM1 HIR1].
            destruct HIR1 as [HIR1 HQ1].
            destruct HQ1 as [HQ1 Hqb1].
            destruct Hqb1 as [Hqb1 HNZT1].
            exists M1. split;auto. split;auto.
            split. lia. split. lia. auto. lia. lia. lia.
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
           { split. auto. split. lia. auto. } 
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
                { eapply g_increase_top_matchable. all:auto.
                  apply H6. apply H5. symmetry;apply H5.
                  symmetry;apply H6. 
                  {
                  apply Sorted_elim2 with (x:=(ask_of m1)) in A0.
                  unfold by_dsp in A0. move /orP in A0. destruct A0.
                  move /leP in H7. lia. move /andP in H7.
                  destruct H7. move /eqP in H7. lia.
                  apply by_dsp_refl. apply H0. destruct H5. eauto.
                  }
                  {
                  apply Sorted_elim2 with (x:=(bid_of m2)) in B0.
                  unfold by_dbp in A0. move /orP in B0. destruct B0.
                  move /leP in H7. lia. move /andP in H7.
                  destruct H7. move /eqP in H7. lia.
                  apply by_dbp_refl. apply H0. destruct H6. eauto.
                  }
                  apply H0.
                 }
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
             lia. eapply g_increase_top_matching_IR.
             all:auto.
                  apply H6. apply H5. symmetry;apply H5.
                  symmetry;apply H6. 
                  {
                  apply Sorted_elim2 with (x:=(ask_of m1)) in A0.
                  unfold by_dsp in A0. move /orP in A0. destruct A0.
                  move /leP in H7. lia. move /andP in H7.
                  destruct H7. move /eqP in H7. lia.
                  apply by_dsp_refl. apply H0. destruct H5. eauto.
                  }
                  {
                  apply Sorted_elim2 with (x:=(bid_of m2)) in B0.
                  unfold by_dbp in A0. move /orP in B0. destruct B0.
                  move /leP in H7. lia. move /andP in H7.
                  destruct H7. move /eqP in H7. lia.
                  apply by_dbp_refl. apply H0. destruct H6. eauto.
                  }
                  apply H0.
             eapply IHk with (M:=M') in H2. destruct H2 as [OPT H2]. 
             destruct H2.  destruct H8. exists OPT. split. auto.
             split. auto. split. rewrite HM'size.
              apply H9. split. lia. all: try apply H7.
              apply H9. 
             apply g_increase_top_NZT. auto.
             apply H5. apply H6. 
          }
          { move /eqP in Haq. assert(ttqa M a < sq a).
            assert(ttqa M a <= sq a). 
            assert(In a (asks_of M)\/~In a (asks_of M)).
            eauto. destruct H6. apply H0. auto.
            apply ttqa_elim in H6. lia. 
            lia.
            destruct H5 as [m H7].
            set (M':=increase_quantb_by_one M m b a).
            assert(Hmatch:matching_in (b::B) (a::A) M').
            { apply increase_quantb_by_one_matching.
              all:auto. apply H7. symmetry;apply H7.
              destruct H7. destruct H7. auto.
            }
            assert(HIR:Is_IR M').
            { apply increase_quantb_by_one_matching_IR.
              all:auto. apply H7. symmetry;apply H7.
              apply H0.
            }
            assert(HQ:QM(M)=QM(M')).
            { apply increase_quantb_by_one_size. all:auto.
              apply H7.
            }
            assert(Hqab:ttq_ab M' b a =1+ ttq_ab M b a).
            { apply increase_quantb_by_one_trade_correct.
              all:auto. apply H7. symmetry;apply H7.
              destruct H7. destruct H7. auto.
            }
            assert(HNZT:(forall m : fill_type, In m M' -> tq m > 0)).
            { apply increase_quantb_by_one_NZT. auto. apply H7. }
            assert(Hqb:ttqb M' b = ttqb M b).
            { apply increase_quantb_by_one_bqb_equal. all:auto.
              apply H7. symmetry;apply H7.
            }
            apply IHk with (M:=M') in Hmatch as HOPT.
            all:auto. destruct HOPT as [M1 HM1]. 
            destruct HM1 as [HM1 HIR1].
            destruct HIR1 as [HIR1 HQ1].
            destruct HQ1 as [HQ1 Hqb1].
            destruct Hqb1 as [Hqb1 HNZT1].
            exists M1. split;auto. split;auto.
            split. lia. split. lia. auto. lia. lia. lia.

          }
        }
      }
Qed.


Lemma MM_exists_opt (B:list Bid)(A:list Ask)(M:list fill_type)(b:Bid)(a:Ask)
(NZT: forall m : fill_type, In m M -> tq m > 0)
(NZA:(forall a0, In a0 (a::A) -> (sq a0) > 0))
(NZB:(forall b0, In b0 (b :: B) -> bq b0 > 0))
(Hanti: (antisymmetric by_dsp)/\(antisymmetric by_dbp))
(NDA:NoDup (idas_of (a::A)))(NDB:NoDup (idbs_of (b::B))):
Sorted by_dbp (b::B) -> 
Sorted by_dsp (a::A) -> 
(matching_in (b::B) (a::A) M) -> 
Is_IR M ->
b>=a ->
QM(M)>=min (bq b) (sq a) ->
(exists OPT, (matching_in (b::B) (a::A) OPT)/\Is_IR OPT/\
(ttq_ab OPT b a = min (bq b) (sq a))/\QM(M)=QM(OPT)/\
(forall m : fill_type, In m OPT -> tq m > 0)).
Proof. intros. 
       assert(exists M', (matching_in (b::B) (a::A) M')/\
       (ttqb M' b >= min (bq b) (QM(M)))/\Is_IR M'/\QM(M)=QM(M')/\
       forall m : fill_type, In m M' -> tq m > 0).
       eapply exists_ttq_top_bid. all:auto. 
       apply Hanti. destruct H5 as [M0 H5].
       destruct H5. destruct H6. destruct H7. 
       destruct (Nat.min (bq b) (sq a) - ttq_ab M0 b a) eqn:Hk.
       {
         eapply MM_exists_opt_k with (k:=0)(A:=A)(a:=a)(B:=B)(b:=b) in H5.
         destruct H5 as [OPT H5]. exists OPT. 
         destruct H5. destruct H9.
         split. apply H5. split. 
         assert (Hmin:ttq_ab OPT b a <= Nat.min (bq b) (sq a)).
         eapply matching_in_elim9 with (B:=(b::B))(A:=(a::A)).
         apply H5. auto.
         split. assert (Hmin:ttq_ab OPT b a <= Nat.min (bq b) (sq a)).
         eapply matching_in_elim9 with (B:=(b::B))(A:=(a::A)).
         all:auto. lia. split. destruct H10. destruct H8. lia.
         apply H10. lia. lia.  apply H8.
       }  
       { assert(Haba:ttqa M0 a >=ttq_ab M0 b a).
         eauto. 
         eapply MM_exists_opt_k with (k:= S n)(A:=A)(a:=a)(B:=B)(b:=b) in H5.
         destruct H5 as [OPT H5]. exists OPT. 
         destruct H5. destruct H9.
         split. apply H5. split. 
         assert (Hmin:ttq_ab OPT b a <= Nat.min (bq b) (sq a)).
         eapply matching_in_elim9 with (B:=(b::B))(A:=(a::A)).
         apply H5. auto.
         split. assert (Hmin:ttq_ab OPT b a <= Nat.min (bq b) (sq a)).
         eapply matching_in_elim9 with (B:=(b::B))(A:=(a::A)).
         all:auto. lia. split. destruct H10. destruct H8. lia.
         apply H10. lia. lia.  apply H8.
       }
Qed. 


Lemma matching_in_elim10 (B:list Bid)(A:list Ask)(M:list fill_type)(a:Ask)(b:Bid)
(NDA:NoDup (a::A))(NDB:NoDup (b::B)):
Sorted by_dsp (a::A) ->
Sorted by_dbp (b::B) ->
b<a ->
matching_in (b::B) (a::A) M ->
~In a (asks_of M).
Proof. intros. induction M as [|m M'].
simpl. eauto.
assert(ask_of m <= bid_of m).
apply H2. auto.
assert(In (ask_of m) (a::A)).
apply H2. simpl. auto.
assert(In (bid_of m) (b::B)).
apply H2. simpl. auto.
destruct H4;destruct H5.
{
subst. lia.
}
{
eapply Sorted_elim2 with (x:=(bid_of m)) in H0.
unfold by_dbp in H0. move /orP in H0.
destruct H0. move /leP in H0. subst. lia.
move /andP in H0. destruct H0. move /eqP in H0.
subst. lia. apply by_dbp_refl. eauto.
}
{
simpl.
intro. destruct H6. subst. lia.
assert(exists m', In m' M'/\a = ask_of m'). eauto.
destruct H7 as [m0 H7]. destruct H7. 
assert(ask_of m0 <= bid_of m0).
apply H2. auto.
eapply Sorted_elim2 with (x:=(bid_of m0)) in H0.
unfold by_dbp in H0. move /orP in H0.
destruct H0. move /leP in H0. subst. lia.
move /andP in H0. destruct H0. move /eqP in H0.
subst. lia. apply by_dbp_refl. apply H2.
simpl. right. eauto.
}
{
intro. simpl in H6. destruct H6.
rewrite H6 in H4. assert(~In a A).
eauto. eauto.
assert(exists m', In m' M'/\a = ask_of m'). eauto.
destruct H7 as [m0 H7]. destruct H7. 
assert(ask_of m0 <= bid_of m0).
apply H2. auto.
eapply Sorted_elim2 with (x:=(bid_of m0)) in H0.
unfold by_dbp in H0. move /orP in H0.
destruct H0. move /leP in H0. subst. lia.
move /andP in H0. destruct H0. move /eqP in H0.
subst. lia. apply by_dbp_refl. apply H2.
simpl. right. eauto.
}
Qed.


Lemma matching_in_elim11 (B:list Bid)(A:list Ask)(M:list fill_type)(a:Ask)(b:Bid)
(NDA:NoDup (a::A))(NDB:NoDup (b::B)):
Sorted by_dsp (a::A) ->
Sorted by_dbp (b::B) ->
b<a ->
matching_in (b::B) (a::A) M ->
matching_in (b::B) A M.
Proof. intros. assert(~In a (asks_of M)).
eapply matching_in_elim10 in H2. all:auto.
split. split. apply H2.
split. apply H2. apply H2.
split. apply H2. assert(asks_of M [<=] a::A).
apply H2. eauto. Qed.




Theorem MM_aux_OPT (B:list Bid)(A:list Ask)(M:list fill_type)
(b:Bid)(a:Ask)(ta tb: nat)
(NDA:NoDup (ida a::(idas_of A)))(NDB:NoDup (idb b::(idbs_of B)))
(NZT: forall m : fill_type, In m M -> tq m > 0)
(NZB: forall b0, In b0 ((Mk_bid (bp b) (btime b) (bq b - tb) (idb b))::B) -> (bq b0)>0)
(NZA: forall a0, In a0 ((Mk_ask (sp a) (stime a) (sq a - ta) (ida a))::A) -> (sq a0)>0)
(Hanti: (antisymmetric by_dsp)/\(antisymmetric by_dbp)):
Sorted by_dbp (b::B) -> 
Sorted by_dsp (a::A) -> 
matching_in ((Mk_bid (bp b) (btime b) (bq b - tb) (idb b))::B)
                        ((Mk_ask (sp a) (stime a) (sq a - ta) (ida a))::A) M ->
Is_IR M -> 
QM(M) <= QM(MM_aux (b::B) (a::A) tb ta).
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
    eapply MM_exists_opt in H5.
    all:auto. 
    destruct H5 as [M0 H5].
    destruct H5. destruct H7. destruct H8. destruct H9. rewrite H9.
    destruct (Nat.eqb (bq b - tb) (sq a - ta)) eqn: Hqabeq.
    {
      simpl. simpl in H8.
      assert(HM0':exists M0', 
      (matching_in l l0 M0')/\Is_IR M0'/\(QM(M0)=QM(M0') + (bq b - tb))/\
      (forall m : fill_type, In m M0' -> tq m > 0)).
      {
        eapply exists_M0_reduced_bid_ask_matching in H5.
        simpl in H5.
        destruct H5 as [M1 H5]. exists M1. split. apply H5.
        split. apply H5. split. apply H5. apply H5.
        auto. simpl.
        move /eqP in Hqabeq. lia.
        auto.
      }
      destruct HM0' as [M0' HM0'].
      replace (QM M0) with (QM M0' + (bq b - tb)).
      cut(QM M0' <= QM (MM_aux l l0 0 0)). lia.
      case l eqn: Hl. simp MM_aux.
      simpl.
      { simp UM_aux.
        simpl.  
        { destruct HM0'. 
          apply matching_on_nilB in H11. 
          rewrite H11.  simpl. lia. }
      }
      case l0 eqn: Hl0. simp MM_aux.
        { simp UM_aux.
          simpl. destruct HM0'. 
          apply matching_on_nilA in H11. 
          rewrite H11.  simpl. lia.
        }
      eapply H with (M:=M0'). all:auto.
      eauto. eauto. apply HM0'. 
      { intros.
        destruct H11. subst b1. simpl. 
        replace (bq b0 - 0) with (bq b0). eauto.
        lia. eauto. 
      }
      { intros.
            destruct H11. subst a1. simpl. 
            replace (sq a0 - 0) with (sq a0). eauto.
            lia. eauto. 
      } 
      eauto. 
      eauto.
      { replace (bq b0 - 0) with (bq b0).
        replace (sq a0 - 0) with (sq a0).
        destruct HM0'. destruct b0;destruct a0. intros. 
        eapply H11.  lia. lia.
      }  
      apply HM0'.
      { replace (bq b0 - 0) with (bq b0).
            assert(Sorted by_dbp (b0 :: l1));eauto;destruct b0;auto.
            lia.
      }
      { replace (sq a0 - 0) with (sq a0). 
        assert(Sorted by_dsp (a0 :: l2));eauto;destruct a0;auto.
        lia. 
      }
     destruct HM0'. destruct H12. destruct H13;auto.
    }
    {
      destruct (Nat.leb (bq b - tb) (sq a - ta)) eqn:Hle.
      {
        simpl. simpl in H6.
        case l eqn: Hl. simp MM_aux. simpl.
        { simp UM_aux.
          simpl. 
          apply matching_on_bnill in H5.
          simpl in H5. lia.
        } 
        assert(HM0':exists M0', (matching_in 
        ((Mk_bid (bp b0) (btime b0) (bq b0 - 0) (idb b0))::l1) 
        ((Mk_ask (sp a) (stime a) (sq a - (ta + (bq b - tb))) (ida a))::l0)
         M0')
        /\Is_IR M0'/\(QM(M0)=QM(M0') + (bq b - tb))/\
          (forall m : fill_type, In m M0' -> tq m > 0)).
        {
         eapply exists_M0_reduced_ask_matching with (b:=
         {|
          bp := b;
          btime := btime b;
          bq := bq b - tb;
          idb := idb b |}) in H5.
         destruct H5 as [M1 H5]. exists M1.
         all:auto. simpl in H5. 
         replace (sq a - (ta + (bq b - tb))) with (sq a - ta - (bq b - tb)).
         replace (bq b0 - 0) with (bq b0). 
         replace ({| bp := b0; btime := btime b0; bq := bq b0; idb := idb b0 |})
         with b0. split. eapply H5. split. apply H5.
         split. apply H5. apply H5.
         destruct b0. simpl. auto.
         lia. lia. simpl in H8. simpl. auto.
         move /leP in Hle. lia. 
         move /eqP in Hqabeq. move /leP in Hle. 
         simpl. lia.
        } 
        destruct HM0' as [M0' HM0'].
        replace (QM M0) with (QM M0' + (bq b - tb)).
        cut(QM M0' <= QM (MM_aux (b0 :: l1) (a :: l0) 0 (ta + (bq b - tb)))).
        lia.
        eapply H0 with (M:=M0'). all:auto.
        eauto. all: try apply HM0'. 
        { move /leP in Hle. intros.
            destruct H11. subst b1. simpl.
            replace (bq b0 - 0) with (bq b0). eauto.
            lia. eauto.
        }
        { move /leP in Hle. intros.
          destruct H11. subst a0. simpl. move /eqP in Hqabeq. lia. eauto. 
        }
        eauto.
        { replace (bq b0 - 0) with (bq b0). destruct b0;auto. eauto. 
            lia.
        } 
        {
        constructor. eauto. intros. simpl.          
        eapply Sorted_elim4 with (x0:=x) in H4.
        destruct a;destruct x. unfold by_dsp. simpl.
        unfold by_dsp in H4. simpl in H4. auto. auto.
        }
        destruct HM0'. destruct H12. destruct H13. lia. 
      }
      {
        simpl. simpl in H6.
        case l0 eqn: Hl0. simp MM_aux. simpl.
        { simp UM_aux.
          simpl. simpl in H5. 
          apply matching_on_anill in H5.
          simpl in H5. simpl. lia.
        } 
        assert(HM0':exists M0', (matching_in 
       ((Mk_bid (bp b) (btime b) (bq b - (tb + (sq a - ta))) (idb b))::l)
       ((Mk_ask (sp a0) (stime a0) (sq a0 - 0) (ida a0))::l1)
       M0')
       /\Is_IR M0'/\(QM(M0)=QM(M0') + (sq a - ta))/\
       (forall m : fill_type, In m M0' -> tq m > 0)).
        {
         eapply exists_M0_reduced_bid_matching with (a:=
         {|
          sp := a;
          stime := stime a;
          sq := sq a - ta;
          ida := ida a |}) in H5. all:auto.
         destruct H5 as [M1 H5]. exists M1.
         destruct H5. simpl in H5. 
         replace (bq b - (tb + (sq a - ta))) with (bq b - tb - (sq a - ta)).
         split. replace (sq a0 - 0) with (sq a0).
         replace ({| sp := a0; stime := stime a0; sq := sq a0; ida := ida a0 |})
         with a0. eapply H5. destruct a0. simpl. auto.
         lia. simpl in H11. split. apply H11. split. apply H11.
         apply H11. lia.
         simpl.
         move /leP in Hle. simpl in H8.  lia. 
         move /eqP in Hqabeq. move /leP in Hle. 
         simpl. lia.
        }
        destruct HM0' as [M0' HM0'].
        replace (QM M0) with (QM M0' + (sq a - ta)).
        cut(QM M0' <= QM (MM_aux (b :: l) (a0 :: l1) (tb + (sq a - ta)) 0)).
        lia.
        eapply H1 with (M:=M0'). all:auto.
        eauto. all: try apply HM0'. 
        { move /leP in Hle. intros.
            destruct H11. subst b0. simpl.
             move /eqP in Hqabeq. lia. eauto.
        }
        { move /leP in Hle. intros.
          destruct H11. subst a1. simpl. 
        replace (sq a0 - 0) with (sq a0). eauto. 
        lia. eauto.
        }
        eauto.
        { constructor. eauto. intros. simpl. 
          eapply Sorted_elim4 with (x0:=x) in H3.
          destruct b;destruct x. unfold by_dsp. simpl.
          unfold by_dsp in H3. simpl in H3. auto. auto.
        }
        { replace (sq a0 - 0) with (sq a0). destruct a0;auto. eauto. 
            lia.
        } 
        destruct HM0'. destruct H12. destruct H13. lia. 
        }
      }
      simpl. move /leP in Hqab. lia. 
    }
  }
  {
  case l0 eqn: Hl0. 
  assert(Hbla:b<a).
  move /leP in Hab. lia.
  apply matching_in_elim11 in H5.
  apply matching_on_nilA in H5. 
  rewrite H5. simpl. lia. eauto. eauto.
  eauto. eauto. auto. apply H2. all:auto. eauto.
  intros. destruct H7. subst a1. simpl. 
  replace (sq a0 - 0) with (sq a0). eauto. lia. eauto.
  eauto. apply matching_in_elim11 in H5. 
  replace (sq a0 - 0) with (sq a0). 
  destruct a0. apply H5. lia. eauto. eauto.
  eauto. eauto. auto. simpl. move /leP in Hab. lia. 
  replace (sq a0 - 0) with (sq a0). destruct a0;auto. eauto. 
  lia.
} 
Qed.

Theorem MM_aux_optimal (B:list Bid)(A:list Ask)(M:list fill_type)
(NZB: forall b, In b B -> (bq b)>0)
(NZA: forall a, In a A -> (sq a)>0)
(NDA:NoDup (idas_of A))
(NDB:NoDup (idbs_of B))
(NZT: forall m : fill_type, In m M -> tq m > 0)
(Hanti: (antisymmetric by_dsp)/\(antisymmetric by_dbp)):
Sorted by_dbp B -> 
Sorted by_dsp A ->
matching_in B A M ->
Is_IR M -> 
QM(M) <= QM(MM_aux B A 0 0).
Proof. intros. case B as [|b B']. 
       {
        simp MM_aux.
        simpl. 
        apply matching_on_nilB in H1. 
        rewrite H1.  simpl. lia.
        }
       case A as [|a A'].
       {
        simp UM_aux.
        simpl. apply matching_on_nilA in H1. 
        rewrite H1.  simpl. lia.
       }        
       apply MM_aux_OPT.
       all:auto.
       { intros. destruct H3. subst b0. simpl.
        replace (bq b - 0) with (bq b). eauto. lia. eauto.
       }
       { intros. destruct H3. subst a0. simpl.
        replace (sq a - 0) with (sq a). eauto. lia. eauto.
       }
       { replace (bq b - 0) with (bq b).
         replace (sq a - 0) with (sq a).
         destruct b. destruct a. simpl. auto.
         lia. lia.
       }
Qed.  


End MM.