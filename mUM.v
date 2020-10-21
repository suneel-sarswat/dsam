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

Section UM.

Definition Is_uniform M B A := (Uniform M /\ matching_in B A M /\ Is_IR M).

Definition optimal_uniform (M : list fill_type)(B: list Bid)(A: list Ask) :=
  Is_uniform M B A /\ 
  (forall M': list fill_type, Is_uniform M' B A -> QM(M') <= QM(M)).


Equations UM_aux (B:list Bid) (A: list Ask) (tb ta: nat): 
(list fill_type) by wf (|B| + |A|):=
UM_aux nil _ _ _:= nil;
UM_aux _ nil _ _:= nil;
UM_aux (b::B') (a::A') tb ta :=  
if (Nat.leb a b) then 
(
 if (Nat.eqb (bq b - tb) (sq a - ta) ) then
  ((Mk_fill b a (bq b - tb) (bp b))::(UM_aux B' A' 0 0))
 else 
  (if (Nat.leb (bq b - tb) (sq a - ta) ) then
    (Mk_fill b a (bq b - tb) (bp b))::(UM_aux B' (a::A') 0 (ta + (bq b - tb))) 
     else
    (Mk_fill b a (sq a - ta) (bp b))::(UM_aux (b::B') A' (tb + (sq a - ta)) 0)  
  )
) else nil. 

Next Obligation.
lia. Qed.
Next Obligation.
lia. Qed.






(*Move this function into other file *)
Fixpoint replace_column (l:list fill_type)(n:nat):=
  match l with
  |nil=>nil
  |m::l'=> ({|bid_of:= bid_of m ; ask_of:= ask_of m ; tq:= tq m ; tp:=n|})::(replace_column l' n)
  end.
(*Move this lemma into other file *)
Lemma replace_column_is_uniform (l: list fill_type)(n:nat):
  uniform (trade_prices_of (replace_column l n)).
Proof. { induction l. simpl.  constructor.
         case l eqn: H. simpl.  constructor. simpl. simpl in IHl. constructor;auto. } Qed.
(*Move this lemma into other file *)
Lemma last_column_is_trade_price (l:list fill_type)(m:fill_type)(n:nat): In m (replace_column l n)->
                                                                  (tp m = n).
Proof. { intro H. induction l. auto. inversion H as [H0 |].  
         inversion H0 as [H1 ]. simpl. exact. apply IHl in H0. exact. } Qed.
(*Move this lemma into other file *)
Lemma replace_column_elim (l: list fill_type)(n:nat): forall m', In m' (replace_column l n)-> exists m, In m l /\ bid_of m = bid_of m' 
/\ ask_of m = ask_of m'.
  Proof. { intros m' H. induction l. 
           { simpl in H. inversion H. }
           { simpl in H. destruct H.
             {  exists a. split. auto. split. subst m'. simpl. auto. subst m'. simpl. auto. }
             { apply IHl in H as H1. destruct H1 as [m H1]. exists m. 
               destruct H1 as [H2 H1]. destruct H1 as [H3 H1]. split.
               auto. split;auto. } } } Qed. 
(*Move this lemma into other file *)
Lemma replace_column_elim_bid (l: list fill_type)(n:nat) (m:fill_type):
In m (replace_column l n) -> In (bid_of m) (bids_of l).
Proof. { induction l. intros. simpl. destruct H.
         intros. simpl in H. simpl. destruct H. left. 
         simpl in H. subst m. simpl. exact. right. apply IHl. exact. } Qed.
(*Move this lemma into other file *)
Lemma replace_column_elim_ask (l: list fill_type)(n:nat) (m:fill_type):
In m (replace_column l n) -> In (ask_of m) (asks_of l).
Proof. { induction l. intros. simpl. destruct H.
         intros. simpl in H. simpl. destruct H. left. 
         simpl in H. subst m. simpl. exact. right. apply IHl. exact. } Qed.
 (*Move this lemma into other file *)
Lemma replace_column_bids (l: list fill_type)(n:nat):
(bids_of l) = (bids_of (replace_column l n)).
  Proof. { induction l. 
           { simpl. auto. }
           { simpl. f_equal. auto. } } Qed. 

(*Move this lemma into other file *)
Lemma replace_column_asks (l: list fill_type)(n:nat):
  (asks_of l) = (asks_of (replace_column l n)).
  Proof. { induction l. 
           { simpl. auto. }
           { simpl. f_equal. auto. } } Qed. 

(*Move this lemma into other file *)
Lemma replace_column_ttqb (l: list fill_type)(b:Bid)(n:nat):
ttqb l b = ttqb (replace_column l n) b.
Proof. induction l. simpl. auto. simpl. 
       destruct (b_eqb b (bid_of a)) eqn:Hba. lia. lia. Qed.
       
(*Move this lemma into other file *)
Lemma replace_column_ttqa (l: list fill_type)(a:Ask)(n:nat):
ttqa l a = ttqa (replace_column l n) a.
Proof. induction l. simpl. auto. simpl. 
       destruct (a_eqb a (ask_of a0)) eqn:Haa0. lia. lia. Qed.

(*Move this lemma into other file *)
Lemma replace_column_size (l: list fill_type)(n:nat):
QM(l) = QM((replace_column l n)).
Proof. induction l. simpl. auto.
simpl. lia. Qed.



Definition uniform_price B A := bp (bid_of (last (UM_aux B A 0 0) m0)).

Lemma UM_aux_subset_bidsB (B: list Bid) (A: list Ask) (tb ta:nat):
  (bids_of (UM_aux B A tb ta)) [<=] B.
  Proof. funelim (UM_aux B A tb ta).
  simp UM_aux. auto. simp UM_aux. auto. 
  simp UM_aux.
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


Lemma UM_aux_subset_asksA (B: list Bid) (A: list Ask) (tb ta:nat):
  (asks_of (UM_aux B A tb ta)) [<=] A.
  Proof. funelim (UM_aux B A tb ta).
  simp UM_aux. auto. simp UM_aux. auto. 
  simp UM_aux.
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

Lemma UM_aux_Sorted_Bids (B: list Bid) (A: list Ask) (tb ta:nat):
  (Sorted by_dbp B -> (Sorted by_dbp (bids_of (UM_aux B A tb ta)))).
  Proof. intros. funelim (UM_aux B A tb ta).
  simp UM_aux. simp UM_aux. simpl. constructor. 
  simp UM_aux.
  destruct (Nat.leb a b) eqn: Hab.
  { destruct (Nat.eqb (bq b - tb) (sq a - ta)) eqn: Heq.
    { simpl. constructor. apply H. eauto. intros.
      assert(In x l). eapply UM_aux_subset_bidsB. eauto.
      eauto.
    }
    { destruct (Nat.leb (bq b - tb) (sq a - ta)) eqn: Hle.
      { simpl. constructor. apply H0. eauto. intros.
        assert(In x l). eapply UM_aux_subset_bidsB. eauto.
        eauto.
      }
      { simpl. constructor. apply H1. eauto. intros.
        assert(In x (b::l)). eapply UM_aux_subset_bidsB. eauto.
        eapply Sorted_elim2 in H2. eauto. eapply by_dbp_refl. 
        auto.
      }
    }
  } 
  simpl. constructor.
Qed.
  
  
  Lemma UM_aux_Sorted_Asks (B: list Bid) (A: list Ask) (tb ta:nat):
    (Sorted by_sp A -> (Sorted by_sp (asks_of (UM_aux B A tb ta)))).
  Proof. intros. funelim (UM_aux B A tb ta).
  simp UM_aux. simpl. constructor. 
  simp UM_aux.
  simp UM_aux.
  destruct (Nat.leb a b) eqn: Hab.
  { destruct (Nat.eqb (bq b - tb) (sq a - ta)) eqn: Heq.
    { simpl. constructor. apply H. eauto. intros.
      assert(In x l0). eapply UM_aux_subset_asksA. eauto.
      eauto.
    }
    { destruct (Nat.leb (bq b - tb) (sq a - ta)) eqn: Hle.
      { simpl. constructor. apply H0. eauto. intros.
        assert(In x (a::l0)). eapply UM_aux_subset_asksA. eauto.
        eapply Sorted_elim2 in H2. eauto. eapply by_sp_refl. 
        auto.
      }
      { simpl. constructor. apply H1. eauto. intros.
        assert(In x l0). eapply UM_aux_subset_asksA. eauto.
        eauto.
      }

    }
  } 
  simpl. constructor.
Qed.

(*Move this lemma into other file *)
Lemma bid_of_last_and_last_of_bids (F: list fill_type)  (b : Bid):
(bid_of (last F m0)) = (last (bids_of F) b0).
Proof.  
induction F as [|m'].  simpl.  auto.  { 
case F eqn:H1. simpl. auto. replace (last (m' :: f :: l) m0) with (last (f :: l) m0). unfold asks_of;fold asks_of. replace
 (last (ask_of m' :: ask_of f :: asks_of l) a0) with
 (last (ask_of f :: asks_of l) a0). exact. symmetry.
 eauto. symmetry. eauto. } Qed.

(*Move this lemma into other file *)
Lemma ask_of_last_and_last_of_asks (F: list fill_type) (a: Ask):
  (ask_of (last F m0)) = (last (asks_of F) a0).
Proof. 

induction F as [|m'].  simpl.  auto.  {
case F eqn:H1. simpl. auto. replace (last (m' :: f :: l) m0) with (last (f :: l) m0). unfold asks_of;fold asks_of. replace
 (last (ask_of m' :: ask_of f :: asks_of l) a0) with
 (last (ask_of f :: asks_of l) a0). exact. symmetry.
 eauto. symmetry. eauto. } Qed.
 
Lemma UM_aux_bid_ge_uniform_price (B: list Bid) (A:list Ask) (b: Bid)  : Sorted by_dbp (B) -> Sorted by_sp (A) -> In b (bids_of (UM_aux B A 0 0)) ->
  b >=(uniform_price B A).
Proof. { intros H1 H2 H3. unfold uniform_price.
         eapply UM_aux_Sorted_Bids  with (A:=A)(ta:=0)(tb:=0) in H1 as H4. 
         assert (H5: by_dbp b (bid_of (last (UM_aux B A 0 0) m0))).
         assert (Hlastb: last (bids_of (UM_aux B A 0 0)) b0 = bid_of (last (UM_aux B A 0 0) m0)).
         symmetry.
         eapply bid_of_last_and_last_of_bids with (F:= ((UM_aux B A 0 0))). auto. rewrite <- Hlastb.
         eapply last_in_Sorted. apply by_dbp_P. apply by_dbp_refl. exact H4. auto.
         unfold by_dbp in H5.  move /orP in H5.
         destruct H5. move /leP in H. auto.
          move /andP in H.
         destruct H. move /eqP in H. lia. } Qed.
  
Lemma UM_aux_bids_ge_asks (B: list Bid) (A:list Ask)(ta tb:nat) (m: fill_type):
In m (UM_aux B A ta tb) -> (bid_of  m) >= (ask_of m).
Proof. { funelim (UM_aux B A ta tb).
{ intros. simp UM_aux in H. elim H. }
{ intros. simp UM_aux in H. elim H. }
{ intros. simp UM_aux in H2. case (Nat.leb a b) eqn: Hab.
 { case (Nat.eqb (bq b - tb) (sq a - ta)) eqn: Heq. 
   { simpl in H2. destruct H2. 
  { subst m. simpl. move /leP in Hab. auto. }
  { eapply H. auto. } }
   { case (Nat.leb (bq b - tb) (sq a - ta)) eqn: Hle. 
 { simpl in H2. destruct H2. 
  { subst m. simpl. move /leP in Hab. auto. }
  { eapply H0. auto. } }
  { simpl in H2. destruct H2. 
  { subst m. simpl. move /leP in Hab. auto. }
  { eapply H1. auto. } } } }
  { elim H2. }}}  Qed.

Lemma UM_aux_ask_le_uniform_price (B: list Bid) (A:list Ask) (a: Ask):
  Sorted by_dbp B -> Sorted by_sp (A) -> In a (asks_of (UM_aux B A 0 0))-> 
  a <= (uniform_price B A).
Proof. { intros H1 H2 H3. unfold uniform_price.
         eapply UM_aux_Sorted_Asks  with (B:=B)(ta:=0)(tb:=0) in H2 as H4. 
         eapply UM_aux_Sorted_Bids  with (A:=A)(ta:=0)(tb:=0) in H1 as H4b. 
         assert (H5: by_sp a (ask_of (last (UM_aux B A 0 0) m0))).
         assert (Hlasta: last (asks_of (UM_aux B A 0 0)) a0 = 
         ask_of (last (UM_aux B A 0 0) m0)).
         symmetry. eapply ask_of_last_and_last_of_asks. auto. auto.
         rewrite <- Hlasta.
         eapply last_in_Sorted. apply by_sp_P. apply by_sp_refl.
         exact H4. auto. unfold by_sp in H5. move /orP in H5. 
         assert (H6: bid_of (last (UM_aux B A 0 0) m0) >= ask_of (last (UM_aux B A 0 0) m0)). 
        { apply UM_aux_bids_ge_asks with (B:=B) (A:=A)(tb:=0)(ta:=0). 
          assert (Hma: exists m, In m (UM_aux B A 0 0) /\ a = ask_of m).
          eauto. destruct Hma as [m Hma].
          apply last_in_list with (x:=m). apply Hma. } 
          { assert (Hma: exists m, In m (UM_aux B A 0 0) /\ a = ask_of m).
          eauto. destruct Hma as [m Hma]. destruct Hma. 
          destruct H5. move /leP in H5. lia. move /andP in H5.
          destruct H5. move /eqP in H5. lia. } } Qed.


Definition UM_matching (B:list Bid) (A:list Ask) : (list fill_type) :=
  replace_column (UM_aux B A 0 0)
                (uniform_price B A). 



Theorem UM_aux_is_Ind_Rat (B: list Bid) (A:list Ask):
  Sorted by_dbp B -> Sorted by_sp A -> Is_IR (UM_matching B A).
Proof. {  intros H1 H2. unfold UM_matching. unfold Is_IR.
          intros m H3. unfold rational. split.
          { assert (H4: tp m = (uniform_price B A)).  
          eapply last_column_is_trade_price. exact H3.
          rewrite  H4. eapply replace_column_elim_bid in H3.
          apply UM_aux_bid_ge_uniform_price. exact. exact. exact. }
          { assert (H4: tp m = (uniform_price B A)).  
          eapply last_column_is_trade_price. exact H3.
          rewrite  H4. eapply replace_column_elim_ask in H3.
          apply UM_aux_ask_le_uniform_price. exact. exact. exact. } } Qed.
(*Move this lemma into other file *)
Lemma IR_UM_matchable_m (M:list fill_type)(m1 m2:fill_type):
  Is_IR M -> Uniform M -> In m1 M -> In m2 M-> bid_of m1 >=ask_of m2. 
Proof. { intros H1 H2 H3 H4. assert (Htp: tp m1 = tp m2). 
         eapply Uniform_elim. exact H2. exact H3. exact H4.
         assert (Htpm1b: tp m1 <= bid_of m1). 
         { unfold Is_IR in H1. unfold rational in H1. eapply H1. exact. }
         assert (Htpm1a: tp m1 >= ask_of m1). 
         { unfold Is_IR in H1. unfold rational in H1. eapply H1. exact. }
         assert (Htpm2b: tp m2 <= bid_of m2). 
         { unfold Is_IR in H1. unfold rational in H1. eapply H1. exact. }
         assert (Htpm2a: tp m2 >= ask_of m2). 
         { unfold Is_IR in H1. unfold rational in H1. eapply H1. exact. }
         lia. } Qed. 


(*
Lemma UM_aux_returns_IR (B: list Bid) (A: list Ask) (NDB: NoDup B) (NDA: NoDup A):
 Sorted by_dbp B -> Sorted by_sp A -> forall m, In m (UM_aux B A 0 0) ->
   (bp (bid_of m))>= (tp m)  /\ (sp (ask_of m)) <= (tp m).
Proof.  { revert NDA. revert A. induction B. intros. split. simpl in H1.
          destruct H1. simpl in H1. destruct H1. intros.
          case A eqn: Ha. simpl in H1. destruct H1.
          simpl in H1.  case (Nat.leb a0 a) eqn: Ha0. simpl in H1.
          destruct H1. subst m. move /leP in Ha0. simpl. eauto. eapply IHB in H1.
          exact. eauto. eauto. eauto. eauto. destruct H1. } Qed.
*)

(*Now we prove that UM_matching is a matching in B A. Note that we have already proved that
  bids of UM is subset of B and asks of UM is subset of A. Furthermore, matchable property 
  is corrolary of IR. So we need to only prove ttqb and ttqa properies of matching. *)

Lemma UM_aux_ttqb_b (B:list Bid) (A:list Ask)(tb ta:nat)(b b0:Bid)
(NDB: NoDup (idbs_of (b::B)))(NDA: NoDup (idas_of A)):
b0<>b ->
In b0 (bids_of (UM_aux (b::B) A tb ta)) ->
ttqb (UM_aux (b::B) A tb ta) b = bq b -tb.
Proof. funelim (UM_aux (b::B) A tb ta). 
  simp UM_aux. simpl. auto.
  simp UM_aux. intros. 
  destruct (Nat.leb a b) eqn: Hab.
  { destruct (Nat.eqb (bq b - tb) (sq a - ta)) eqn: Heq.
    { simpl. destruct (b_eqb b b) eqn: Hbb. 
      cut(ttqb (UM_aux l l0 0 0) b= 0). lia.
      assert(~In b l). eapply idbs_of_nodup in NDB as NDBb. 
      eauto. assert(~In b (bids_of (UM_aux l l0 0 0))).
      assert((bids_of (UM_aux l l0 0 0)) [<=] l).
      eapply UM_aux_subset_bidsB.
      eauto. apply ttqb_elim in H5. lia.
      move /eqP in Hbb. elim Hbb. auto.
    }
    { destruct (Nat.leb (bq b - tb) (sq a - ta)) eqn: Hle.
      { simpl. destruct (b_eqb b b) eqn: Hbb. 
      cut(ttqb (UM_aux l (a :: l0) 0 (ta + (bq b - tb))) b= 0). lia.
      assert(~In b l). eapply idbs_of_nodup in NDB as NDBb. 
      eauto. assert(~In b (bids_of (UM_aux l (a :: l0) 0 (ta + (bq b - tb))))).
      assert((bids_of (UM_aux l (a :: l0) 0 (ta + (bq b - tb)))) [<=] l).
      eapply UM_aux_subset_bidsB.
      eauto. apply ttqb_elim in H5. lia.
      move /eqP in Hbb. elim Hbb. auto.
    }
    { simpl. simpl in H3. destruct H3. subst b1. elim H2. auto.
      destruct (b_eqb b b) eqn: Hbb. specialize (H1 b1). rewrite H1.
      eauto. eauto. auto. auto. move /leP in Hle. lia.
      move /eqP in Hbb. elim Hbb. auto.
    }
  }
}
simpl in H3. auto.
Qed.

Lemma UM_aux_ttqb_b_le (B:list Bid) (A:list Ask)(tb ta:nat)(b:Bid)
(NDB: NoDup (idbs_of (b::B)))(NDA: NoDup (idas_of A)):
ttqb (UM_aux (b::B) A tb ta) b <= bq b - tb.
Proof. funelim (UM_aux (b::B) A tb ta). 
  simp UM_aux. simpl. lia.
  simp UM_aux. 
  destruct (Nat.leb a b) eqn: Hab.
  { destruct (Nat.eqb (bq b - tb) (sq a - ta)) eqn: Heq.
    { simpl. destruct (b_eqb b b) eqn: Hbb. 
      cut(ttqb (UM_aux l l0 0 0) b= 0). lia.
      assert(~In b l). eapply idbs_of_nodup in NDB as NDBb. 
      eauto. assert(~In b (bids_of (UM_aux l l0 0 0))).
      assert((bids_of (UM_aux l l0 0 0)) [<=] l).
      eapply UM_aux_subset_bidsB.
      eauto. apply ttqb_elim in H3. lia.
      move /eqP in Hbb. elim Hbb. auto.
    }
    { destruct (Nat.leb (bq b - tb) (sq a - ta)) eqn: Hle.
      { simpl. destruct (b_eqb b b) eqn: Hbb. 
      cut(ttqb (UM_aux l (a :: l0) 0 (ta + (bq b - tb))) b= 0). lia.
      assert(~In b l). eapply idbs_of_nodup in NDB as NDBb. 
      eauto. assert(~In b (bids_of (UM_aux l (a :: l0) 0 (ta + (bq b - tb))))).
      assert((bids_of (UM_aux l (a :: l0) 0 (ta + (bq b - tb)))) [<=] l).
      eapply UM_aux_subset_bidsB.
      eauto. apply ttqb_elim in H3. lia.
      move /eqP in Hbb. elim Hbb. auto.
    }
    { simpl. destruct (b_eqb b b) eqn: Hbb. assert (NoDup (idas_of l0)).
      eauto. apply H1 in H2. move /leP in Hle. lia. eauto.
      move /eqP in Hbb. elim Hbb. auto.
    }
  }
}
simpl. lia.
Qed.

Lemma UM_aux_ttqb_b0 (B:list Bid) (A:list Ask)(tb ta:nat)(b b0:Bid)
(NDB: NoDup (idbs_of (b::B)))(NDA: NoDup (idas_of A)):
b0<>b ->
ttqb (UM_aux (b::B) A tb ta) b0 <= bq b0.
Proof. funelim (UM_aux (b::B) A tb ta). 
  simp UM_aux. simpl. intros. lia.
  simp UM_aux. intros. simpl. destruct (b_eqb b1 b) eqn: Hb1b.
  move /eqP in Hb1b. subst b1. elim H2. auto.
  destruct (Nat.leb a b) eqn: Hab.
  { destruct (Nat.eqb (bq b - tb) (sq a - ta)) eqn: Heq.
    { simpl. rewrite Hb1b. destruct l. simp UM_aux. 
      simpl. lia. 
      destruct (b_eqb b1 b0) eqn:Hb1b0. move /eqP in Hb1b0.
      subst b0. replace (bq b1) with (bq b1 - 0). 
      eapply UM_aux_ttqb_b_le with (b:=b1)(tb:=0). eauto.
      eauto. lia.  move /eqP in Hb1b0. eapply H in Hb1b0. eauto.
      eauto. eauto. auto. auto.
    }
    { destruct (Nat.leb (bq b - tb) (sq a - ta)) eqn: Hle.
      { simpl. rewrite Hb1b. destruct l. simp UM_aux. 
        simpl. lia. 
        destruct (b_eqb b1 b0) eqn:Hb1b0. move /eqP in Hb1b0.
        subst b0. replace (bq b1) with (bq b1 - 0). 
        eapply UM_aux_ttqb_b_le with (b:=b1)(tb:=0). eauto.
        eauto. lia.  move /eqP in Hb1b0. eapply H0 in Hb1b0. eauto.
        eauto. eauto. auto. auto.
      }
      { simpl. rewrite Hb1b. move /eqP in Hb1b. eapply H1 in Hb1b. auto.
        eauto. eauto.
    }
  }
}
simpl. lia.
Qed.

Lemma UM_aux_ttqb (B:list Bid) (A:list Ask)(b:Bid)
(NDB: NoDup (idbs_of B))(NDA: NoDup (idas_of A)):
ttqb (UM_aux B A 0 0) b <= bq b.
Proof. destruct B. simp UM_aux. simpl. lia.
       destruct (b_eqb b0 b) eqn: Hb. 
       move /eqP in Hb.
       subst. replace (bq b) with (bq b - 0).
       eapply UM_aux_ttqb_b_le with (tb:=0)(ta:=0)(A:=A)(B:=B)(b:=b).
       eauto. eauto. lia. 
       move /eqP in Hb.
       apply UM_aux_ttqb_b0. eauto. eauto. auto. Qed.

(*begin: ttqa*)

Lemma UM_aux_ttqa_a (B:list Bid) (A:list Ask)(tb ta:nat)(a a0:Ask)
(NDB: NoDup (idbs_of (B)))(NDA: NoDup (idas_of (a::A))):
a0<>a ->
In a0 (asks_of (UM_aux (B) (a::A) tb ta)) ->
ttqa (UM_aux (B) (a::A) tb ta) a = sq a -ta.
Proof. funelim (UM_aux (B) (a::A) tb ta). 
  simp UM_aux. simpl. auto.
  simp UM_aux. intros. 
  destruct (Nat.leb a b) eqn: Hab.
  { destruct (Nat.eqb (bq b - tb) (sq a - ta)) eqn: Heq.
    { simpl. destruct (a_eqb a a) eqn: Haa. 
      cut(ttqa (UM_aux l l0 0 0) a= 0). 
      move /eqP in Heq. lia.
      assert(~In a l0). eapply idas_of_nodup in NDA as NDAa. 
      eauto. assert(~In a (asks_of (UM_aux l l0 0 0))).
      assert((asks_of (UM_aux l l0 0 0)) [<=] l0).
      eapply UM_aux_subset_asksA.
      eauto. apply ttqa_elim in H5. lia.
      move /eqP in Haa. elim Haa. auto.
    }
    { destruct (Nat.leb (bq b - tb) (sq a - ta)) eqn: Hle.
      { simpl. simpl in H3. destruct H3. subst a1. elim H2. auto.
        destruct (a_eqb a a) eqn: Haa. specialize (H0 a1). rewrite H0.
        eauto. eauto. auto. auto. move /leP in Hle. lia.
        move /eqP in Haa. elim Haa. auto.
      }
      { simpl. destruct (a_eqb a a) eqn: Haa. 
        cut(ttqa (UM_aux (b :: l) l0 (tb + (sq a - ta)) 0) a= 0).
        lia. 
        assert(~In a l0). eapply idas_of_nodup in NDA as NDAa. 
        eauto. assert(~In a (asks_of (UM_aux (b::l) (l0) (tb + (sq a - ta)) 0))).
        assert((asks_of (UM_aux (b::l) (l0) (tb + (sq a - ta)) 0)) [<=] l0).
        eapply UM_aux_subset_asksA.
        eauto. apply ttqa_elim in H5. lia.
        move /eqP in Haa. elim Haa. auto.
    }
  }
}
simpl in H3. auto.
Qed.

Lemma UM_aux_ttqa_a_le (B:list Bid) (A:list Ask)(tb ta:nat)(a:Ask)
(NDB: NoDup (idbs_of (B)))(NDA: NoDup (idas_of (a::A))):
ttqa (UM_aux (B) (a::A) tb ta) a <= sq a - ta.
Proof. funelim (UM_aux (B) (a::A) tb ta). 
  simp UM_aux. simpl. lia.
  simp UM_aux. 
  destruct (Nat.leb a b) eqn: Hab.
  { destruct (Nat.eqb (bq b - tb) (sq a - ta)) eqn: Heq.
    { simpl. destruct (a_eqb a a) eqn: Haa. 
      cut(ttqa (UM_aux l l0 0 0) a= 0). 
      move /eqP in Heq. lia.
      assert(~In a l0). eapply idas_of_nodup in NDA as NDAa. 
      eauto. assert(~In a (asks_of (UM_aux l l0 0 0))).
      assert((asks_of (UM_aux l l0 0 0)) [<=] l0).
      eapply UM_aux_subset_asksA.
      eauto. apply ttqa_elim in H3. lia.
      move /eqP in Haa. elim Haa. auto.
    }
    { destruct (Nat.leb (bq b - tb) (sq a - ta)) eqn: Hle.
      { simpl. destruct (a_eqb a a) eqn: Haa. assert (NoDup (idbs_of l)).
        eauto. apply H0 in H2. move /leP in Hle. lia. eauto.
        move /eqP in Haa. elim Haa. auto.
      }
      { simpl. destruct (a_eqb a a) eqn: Haa. 
        cut(ttqa (UM_aux (b :: l) l0 (tb + (sq a - ta)) 0) a= 0). 
        move /eqP in Heq. lia.
        assert(~In a l0). eapply idas_of_nodup in NDA as NDAa. 
        eauto. assert(~In a (asks_of (UM_aux (b :: l) l0 (tb + (sq a - ta)) 0))).
        assert(asks_of (UM_aux (b :: l) l0 (tb + (sq a - ta)) 0) [<=] l0).
        eapply UM_aux_subset_asksA.
        eauto. apply ttqa_elim in H3. lia.
        move /eqP in Haa. elim Haa. auto.
      }
    }
  }
simpl. lia.
Qed.

Lemma UM_aux_ttqa_a0 (B:list Bid) (A:list Ask)(tb ta:nat)(a a0:Ask)
(NDB: NoDup (idbs_of (B)))(NDA: NoDup (idas_of (a::A))):
a0<>a ->
ttqa (UM_aux (B) (a::A) tb ta) a0 <= sq a0.
Proof. funelim (UM_aux (B) (a::A) tb ta). 
  simp UM_aux. simpl. intros. lia.
  simp UM_aux. intros. simpl. destruct (a_eqb a1 a) eqn: Ha1a.
  move /eqP in Ha1a. subst a1. elim H2. auto.
  destruct (Nat.leb a b) eqn: Hab.
  { destruct (Nat.eqb (bq b - tb) (sq a - ta)) eqn: Heq.
    { simpl. rewrite Ha1a. destruct l0. 
      destruct l. simp UM_aux. simpl. lia. simp UM_aux. simpl. lia.
      destruct (a_eqb a1 a0) eqn:Ha1a0. move /eqP in Ha1a0.
      subst a0. replace (sq a1) with (sq a1 - 0). 
      eapply UM_aux_ttqa_a_le with (a:=a1)(ta:=0). eauto.
      eauto. lia.  move /eqP in Ha1a0. eapply H in Ha1a0. eauto.
      eauto. eauto. auto. auto.
    }
    { destruct (Nat.leb (bq b - tb) (sq a - ta)) eqn: Hle.
      { simpl. rewrite Ha1a. move /eqP in Ha1a. eapply H0 in Ha1a. auto.
        eauto. eauto.
      }
      { simpl. rewrite Ha1a. destruct l0. simp UM_aux. 
        simpl. lia. 
        destruct (a_eqb a1 a0) eqn:Ha1a0. move /eqP in Ha1a0.
        subst a0. replace (sq a1) with (sq a1 - 0). 
        eapply UM_aux_ttqa_a_le with (a:=a1)(ta:=0). eauto.
        eauto. lia.  move /eqP in Ha1a0. eapply H1 in Ha1a0. eauto.
        eauto. eauto. auto. auto.
      }
  }
}
simpl. lia.
Qed.



Lemma UM_aux_ttqa (B:list Bid) (A:list Ask)(a:Ask)
(NDB: NoDup (idbs_of B))(NDA: NoDup (idas_of A)):
ttqa (UM_aux B A 0 0) a <= sq a.
Proof. destruct A. simp UM_aux. simpl. 
       destruct B. simp UM_aux. simpl. lia. simp UM_aux. simpl. lia.
       destruct (a_eqb a0 a) eqn: Ha. 
       move /eqP in Ha.
       subst. replace (sq a) with (sq a - 0).
       eapply UM_aux_ttqa_a_le with (tb:=0)(ta:=0)(A:=A)(B:=B)(a:=a).
       eauto. eauto. lia. 
       move /eqP in Ha.
       apply UM_aux_ttqa_a0. eauto. eauto. auto. Qed.



Theorem UM_Is_Matching (B:list Bid)(A:list Ask)
(NDB: NoDup (idbs_of B))(NDA: NoDup (idas_of A)):
Sorted by_dbp B -> Sorted by_sp (A) -> Is_uniform (UM_matching B A) B A.
Proof. intros. split. 
               { unfold UM_matching. apply replace_column_is_uniform. }
               { split.
                 { split. 
                    { split. 
                      { unfold All_matchable.
                        intros. eapply UM_aux_is_Ind_Rat with (A:=A) in H.
                        unfold Is_IR in H. apply H in H1.
                        unfold rational in H1. lia. auto.
                      }
                      { split.
                       { intros. unfold UM_matching.
                         simpl. 
                         replace (ttqb (replace_column (UM_aux B A 0 0)
                         (uniform_price B A)) b) with (ttqb (UM_aux B A 0 0) b).
                         apply UM_aux_ttqb. auto. auto. 
                         apply replace_column_ttqb.
                       }
                       { intros. unfold UM_matching.
                         simpl. 
                         replace (ttqa (replace_column (UM_aux B A 0 0)
                         (uniform_price B A)) a) with (ttqa (UM_aux B A 0 0) a).
                         apply UM_aux_ttqa. auto. auto. 
                         apply replace_column_ttqa.
                       } 
                     }
                   }
                   { split. unfold UM_matching.
                     replace (bids_of (replace_column (UM_aux B A 0 0)
                     (uniform_price B A))) with (bids_of (UM_aux B A 0 0)).
                     apply UM_aux_subset_bidsB.
                     apply replace_column_bids.
                     unfold UM_matching.
                     replace (asks_of (replace_column (UM_aux B A 0 0)
                     (uniform_price B A))) with (asks_of (UM_aux B A 0 0)).
                     apply UM_aux_subset_asksA.
                     apply replace_column_asks.
                   }
                }
                { eapply UM_aux_is_Ind_Rat with (A:=A) in H.
                  auto. auto. 
                }
             }
          Qed.


(*Now we prove fairness of UM.*)


Lemma UM_aux_ttqb_fair_bid_t (B:list Bid) (A:list Ask)(tb ta:nat)(b b1 b2:Bid)
(NDB: NoDup (idbs_of (b::B)))(NDA: NoDup (idas_of A)):
Sorted by_dbp (b::B) -> 
Sorted by_sp  A -> 
b1>b2 -> 
In b1 (bids_of (UM_aux (b::B) A tb ta)) -> 
In b2 (bids_of (UM_aux (b::B) A tb ta)) ->  
(b1=b -> ttqb (UM_aux (b::B) A tb ta) b1 = bq b1 - tb )/\
(b1<>b->ttqb (UM_aux (b::B) A tb ta) b1 = bq b1 ).
Proof. funelim (UM_aux (b::B) A tb ta). auto.
{ intros. destruct (b_eqb b1 b ) eqn: Hbb1. 
  { move /eqP in Hbb1. subst b1. split.
    intros. eapply UM_aux_ttqb_b with (b0:=b2). auto. auto. 
    destruct (b_eqb b b2) eqn:Hb0b. move /eqP in Hb0b.
    subst b. destruct b2. simpl in H4. lia.
    move /eqP in Hb0b. auto. auto. intros. 
    elim H7. auto. 
  }
  { split;intros. 
    { subst b1. move /eqP in Hbb1. auto. }
    { rewrite<- Heqcall.  
      destruct (Nat.leb a b) eqn: Hab.
      { destruct (Nat.eqb (bq b - tb) (sq a - ta)) eqn: Heq.
        { simpl. rewrite Hbb1. 
          rewrite<- Heqcall in H5. simpl in H5. 
          rewrite<- Heqcall in H6. simpl in H6. 
          destruct H5;destruct H6.
          { subst b1;auto. }
          { subst b1;auto. }
          { subst b2. assert (In b1 l). 
            eapply UM_aux_subset_bidsB. eauto.
            assert(b>b1). 
            { eapply Sorted_elim4 with (a0:=b)(x:=b1)(lr:=by_dbp) in H2. 
              unfold by_dbp in H2. move /orP in H2. destruct H2. 
              move /leP in H2. lia. move /andP in H2;destruct H2.
              move /eqP in H2. lia. auto.  } 
              lia. }
          { case l as [| b0 B'] eqn:Hl.
            { simp UM_aux in H5. simpl in H4. auto. }
            { destruct (b_eqb b1 b0) eqn: Hbb0. 
              { move /eqP in Hbb0. subst b0. replace (bq b1) with (bq b1 - 0). 
                eapply UM_aux_ttqb_b with (b0:=b2).
                eauto. eauto. 
                destruct (b_eqb b2 b1) eqn:Hb2b1. move /eqP in Hb2b1.
                subst b1. destruct b2. simpl in H4. lia.
                move /eqP in Hb2b1. auto. auto. lia.
              }
              { move /eqP in Hbb0. eapply H in Hbb0.
                all: eauto. 
              } 
            }
          }
        } 
        { destruct (Nat.leb (bq b - tb) (sq a - ta)) eqn: Hle.
          { simpl. rewrite Hbb1.           
            rewrite<- Heqcall in H5. simpl in H5. 
            rewrite<- Heqcall in H6. simpl in H6. 
            destruct H5;destruct H6.
            { subst b1;auto. }
            { subst b1;auto. }
            { subst b2. assert (In b1 l). 
              eapply UM_aux_subset_bidsB. eauto.
              assert(b>b1). 
              { eapply Sorted_elim4 with (a0:=b)(x:=b1)(lr:=by_dbp) in H2. 
                unfold by_dbp in H2. move /orP in H2. destruct H2. 
                move /leP in H2. lia. move /andP in H2;destruct H2.
                move /eqP in H2. lia. auto.  
              } 
              lia. 
            }
            { case l as [| b0 B'] eqn:Hl.
              { simp UM_aux in H5. simpl in H4. auto. }
              { destruct (b_eqb b1 b0) eqn: Hbb0. 
                { move /eqP in Hbb0. subst b0. replace (bq b1) with (bq b1 - 0). 
                  eapply UM_aux_ttqb_b with (b0:=b2).
                  eauto. eauto. 
                  destruct (b_eqb b2 b1) eqn:Hb2b1. move /eqP in Hb2b1.
                  subst b1. destruct b2. simpl in H4. lia.
                  move /eqP in Hb2b1. auto. auto. lia.
                }
                { move /eqP in Hbb0. eapply H0 in Hbb0.
                  all: eauto. 
                } 
              }
            }
          }
          { simpl. rewrite Hbb1. 
            rewrite<- Heqcall in H5. simpl in H5. 
            rewrite<- Heqcall in H6. simpl in H6. 
            destruct H5;destruct H6.
            { subst b1;auto. }
            { subst b1;auto. }
            { subst b2. assert (In b1 (b::l)). 
              eapply UM_aux_subset_bidsB. eauto.
              assert(b>b1). 
              { eapply Sorted_elim4 with (a0:=b)(x:=b1)(lr:=by_dbp) in H2. 
                unfold by_dbp in H2. move /orP in H2. destruct H2. 
                move /leP in H2. lia. move /andP in H2;destruct H2.
                move /eqP in H2. lia. destruct H6.
                subst b. elim H7. auto. auto.  
              } 
              lia. 
            }
            { eapply H1 in H7. all: eauto. 
            }
          }
        }
      }
      { rewrite<- Heqcall in H5. simpl in H5. auto.
      }
    }
  }
}
Qed.



Lemma UM_aux_ttqb_fair_ask_t (B:list Bid) (A:list Ask)(tb ta:nat)(a a1 a2:Ask)
(NDB: NoDup (idbs_of B))(NDA: NoDup (idas_of (a::A))):
Sorted by_dbp (B) -> 
Sorted by_sp  (a::A) -> 
a1<a2 -> 
In a1 (asks_of (UM_aux (B) (a::A) tb ta)) -> 
In a2 (asks_of (UM_aux (B) (a::A) tb ta)) ->  
(a1=a -> ttqa (UM_aux (B) (a::A) tb ta) a1 = sq a1 - ta )/\
(a1<>a->ttqa (UM_aux (B) (a::A) tb ta) a1 = sq a1 ).
Proof. funelim (UM_aux (B) (a::A) tb ta). auto.
{ intros. destruct (a_eqb a1 a ) eqn: Haa1. 
  { move /eqP in Haa1. subst a1. split.
    intros. eapply UM_aux_ttqa_a with (a0:=a2). auto. auto. 
    destruct (a_eqb a a2) eqn:Ha0a. move /eqP in Ha0a.
    subst a. destruct a2. simpl in H4. lia.
    move /eqP in Ha0a. auto. auto. intros. 
    elim H7. auto. 
  }
  { split;intros. 
    { subst a1. move /eqP in Haa1. auto. }
    { rewrite<- Heqcall.  
      destruct (Nat.leb a b) eqn: Hab.
      { destruct (Nat.eqb (bq b - tb) (sq a - ta)) eqn: Heq.
        { simpl. rewrite Haa1. 
          rewrite<- Heqcall in H5. simpl in H5. 
          rewrite<- Heqcall in H6. simpl in H6. 
          destruct H5;destruct H6.
          { subst a1;auto. }
          { subst a1;auto. }
          { subst a2. assert (In a1 l0). 
            eapply UM_aux_subset_asksA. eauto.
            assert(a<a1). 
            { eapply Sorted_elim4 with (a0:=a)(x:=a1)(lr:=by_sp) in H3. 
              unfold by_sp in H3. move /orP in H3. destruct H3. 
              move /leP in H3. lia. move /andP in H3;destruct H3.
              move /eqP in H3. lia. auto.  } 
              lia. }
          { case l0 as [| a0 A'] eqn:Hl0.
            { destruct l. simp UM_aux in H5. simpl in H5. auto.
               simp UM_aux in H5. simpl in H5. auto. }
            { destruct (a_eqb a1 a0) eqn: Haa0. 
              { move /eqP in Haa0. subst a0. replace (sq a1) with (sq a1 - 0). 
                eapply UM_aux_ttqa_a with (a0:=a2).
                eauto. eauto. 
                destruct (a_eqb a2 a1) eqn:Ha2a1. move /eqP in Ha2a1.
                subst a1. destruct a2. simpl in H4. lia.
                move /eqP in Ha2a1. auto. auto. lia.
              }
              { move /eqP in Haa0. eapply H in Haa0.
                all: eauto. 
              } 
            }
          }
        } 
        { destruct (Nat.leb (bq b - tb) (sq a - ta)) eqn: Hle.
          { simpl. rewrite Haa1. 
            rewrite<- Heqcall in H5. simpl in H5. 
            rewrite<- Heqcall in H6. simpl in H6. 
            destruct H5;destruct H6.
            { subst a1;auto. }
            { subst a1;auto. }
            { subst a2. assert (In a1 (a::l0)). 
              eapply UM_aux_subset_asksA. eauto.
              assert(a<a1). 
              { eapply Sorted_elim4 with (a0:=a)(x:=a1)(lr:=by_sp) in H3. 
                unfold by_sp in H3. move /orP in H3. destruct H3. 
                move /leP in H3. lia. move /andP in H3;destruct H3.
                move /eqP in H3. lia. destruct H6.
                subst a. elim H7. auto. auto.  
              } 
              lia. 
            }
            { eapply H0 in H7. all: eauto. 
            }
          }
          { simpl. rewrite Haa1.           
            rewrite<- Heqcall in H5. simpl in H5. 
            rewrite<- Heqcall in H6. simpl in H6. 
            destruct H5;destruct H6.
            { subst a1;auto. }
            { subst a1;auto. }
            { subst a2. assert (In a1 l0). 
              eapply UM_aux_subset_asksA. eauto.
              assert(a<a1). 
              { eapply Sorted_elim4 with (a0:=a)(x:=a1)(lr:=by_sp) in H3. 
                unfold by_sp in H3. move /orP in H3. destruct H3. 
                move /leP in H3. lia. move /andP in H3;destruct H3.
                move /eqP in H3. lia. auto.  
              } 
              lia. 
            }
            { case l0 as [| a0 A'] eqn:Hl0.
              { destruct l. simp UM_aux in H5. simpl in H5. auto.
                simp UM_aux in H5. simpl in H5. auto. }
              { destruct (a_eqb a1 a0) eqn: Haa0. 
                { move /eqP in Haa0. subst a0. replace (sq a1) with (sq a1 - 0). 
                  eapply UM_aux_ttqa_a with (a0:=a2).
                  eauto. eauto. 
                  destruct (a_eqb a2 a1) eqn:Ha2a1. move /eqP in Ha2a1.
                  subst a1. destruct a2. simpl in H4. lia.
                  move /eqP in Ha2a1. auto. auto. lia.
                }
                { move /eqP in Haa0. eapply H1 in Haa0.
                  all: eauto. 
                } 
              }
            }
          }
          
        }
      }
      { rewrite<- Heqcall in H5. simpl in H5. auto.
      }
    }
  }
}
Qed.

Lemma UM_aux_fair_bid_in (B:list Bid) (A:list Ask)(tb ta:nat)(b1 b2:Bid)
(NDB: NoDup (idbs_of B))(NDA: NoDup (idas_of A)):
Sorted by_dbp B -> 
Sorted by_sp  A -> 
b1>b2 -> 
In b2 (bids_of (UM_aux B A tb ta)) -> 
In b1 B ->
In b1 (bids_of (UM_aux B A tb ta)).
Proof. funelim (UM_aux B A tb ta). auto. auto.
{ intros. rewrite<- Heqcall. 
      rewrite<- Heqcall in H5. 
      destruct (Nat.leb a b) eqn: Hab.
      { destruct (Nat.eqb (bq b - tb) (sq a - ta)) eqn: Heq.
        { simpl. simpl in H5.  
          destruct H5.
          { subst b2. destruct H6. auto. 
            assert(b>b1). 
            { eapply Sorted_elim4 with (a0:=b)(x:=b1)(lr:=by_dbp) in H2. 
              unfold by_dbp in H2. move /orP in H2. destruct H2. 
              move /leP in H2. lia. move /andP in H2;destruct H2.
              move /eqP in H2. lia. auto.  } 
              lia. 
          }
          { destruct H6. auto.  right. eapply H with (b2:=b2). 
            all: auto. all: eauto. 
          }
        } 
        { destruct (Nat.leb (bq b - tb) (sq a - ta)) eqn: Hle.
          { simpl. simpl in H5.  
            destruct H5.
            { subst b2. destruct H6. auto. 
              assert(b>b1). 
              { eapply Sorted_elim4 with (a0:=b)(x:=b1)(lr:=by_dbp) in H2. 
                unfold by_dbp in H2. move /orP in H2. destruct H2. 
                move /leP in H2. lia. move /andP in H2;destruct H2.
                move /eqP in H2. lia. auto.  } 
                lia. 
            }
            { destruct H6. auto.  right. eapply H0 with (b2:=b2). 
              all: auto. all: eauto. 
            }
          } 
          { simpl. simpl in H5.  
            destruct H5.
            { subst b2. destruct H6. auto.
            assert(b>b1). 
              { eapply Sorted_elim4 with (a0:=b)(x:=b1)(lr:=by_dbp) in H2. 
                unfold by_dbp in H2. move /orP in H2. destruct H2. 
                move /leP in H2. lia. move /andP in H2;destruct H2.
                move /eqP in H2. lia. auto.  } 
                lia. 
            }
            { destruct H6. auto. right. eapply H1 with (b2:=b2).
              all: auto. all: eauto.
            }
          }
        }
      }
      {  simpl in H5. auto.
      }
    }
Qed.

Lemma UM_aux_fair_ask_in (B:list Bid) (A:list Ask)(tb ta:nat)(a1 a2:Ask)
(NDB: NoDup (idbs_of B))(NDA: NoDup (idas_of A)):
Sorted by_dbp B -> 
Sorted by_sp  A -> 
a1<a2 -> 
In a2 (asks_of (UM_aux B A tb ta)) -> 
In a1 A ->
In a1 (asks_of (UM_aux B A tb ta)).
Proof. funelim (UM_aux B A tb ta). auto. auto.
{ intros. rewrite<- Heqcall. 
      rewrite<- Heqcall in H5. 
      destruct (Nat.leb a b) eqn: Hab.
      { destruct (Nat.eqb (bq b - tb) (sq a - ta)) eqn: Heq.
        { simpl. simpl in H5.  
          destruct H5.
          { subst a2. destruct H6. auto. 
            assert(a<a1). 
            { eapply Sorted_elim4 with (a0:=a)(x:=a1)(lr:=by_sp) in H3. 
              unfold by_sp in H3. move /orP in H3. destruct H3. 
              move /leP in H3. lia. move /andP in H3;destruct H3.
              move /eqP in H3. lia. auto.  } 
              lia. 
          }
          { destruct H6. auto.  right. eapply H with (a2:=a2). 
            all: auto. all: eauto. 
          }
        } 
        { destruct (Nat.leb (bq b - tb) (sq a - ta)) eqn: Hle.
          { simpl. simpl in H5.  
            destruct H5.
            { subst a2. destruct H6. auto. 
              assert(a<a1). 
              { eapply Sorted_elim4 with (a0:=a)(x:=a1)(lr:=by_sp) in H3. 
                unfold by_sp in H3. move /orP in H3. destruct H3.  
                move /leP in H3. lia. move /andP in H3;destruct H3.
                move /eqP in H3. lia. auto.  } 
                lia. 
            }
            { destruct H6. auto.  right. eapply H0 with (a2:=a2). 
              all: auto. all: eauto. 
            }
          } 
          { simpl. simpl in H5.  
            destruct H5.
            { subst a2. destruct H6. auto.
            assert(a<a1). 
              { eapply Sorted_elim4 with (a0:=a)(x:=a1)(lr:=by_sp) in H3. 
                unfold by_sp in H3. move /orP in H3. destruct H3.  
                move /leP in H3. lia. move /andP in H3;destruct H3.
                move /eqP in H3. lia. auto.  } 
                lia. 
            }
            { destruct H6. auto. right. eapply H1 with (a2:=a2).
              all: auto. all: eauto.
            }
          }
        }
      }
      {  simpl in H5. auto.
      }
    }
Qed.



Theorem UM_Fair (B:list Bid)(A:list Ask)
(NDB: NoDup (idbs_of B))(NDA: NoDup (idas_of A)):
Sorted by_dbp B -> Sorted by_sp (A) -> Is_fair (UM_matching B A) B A.
Proof. intros. unfold Is_fair.
               { split.
                 { unfold UM_matching. unfold fair_on_asks.
                   intros. split.
                   { replace (asks_of (replace_column 
                     (UM_aux B (A) 0 0) (uniform_price B (A)))) with
                     (asks_of (UM_aux B (A) 0 0)).
                      replace (asks_of (replace_column 
                     (UM_aux B (A) 0 0) (uniform_price B (A)))) with
                     (asks_of (UM_aux B (A) 0 0)) in H3. 
                     eapply UM_aux_fair_ask_in. all:auto. eauto. auto.
                     apply H1. apply replace_column_asks.
                     apply replace_column_asks. }
                   { replace (ttqa (replace_column 
                     (UM_aux B A 0 0) (uniform_price B A)) s) with
                     (ttqa (UM_aux B A 0 0) s). 
                      case A as [|a A']. simpl in H1. 
                      destruct H1. auto. destruct (a_eqb a s) eqn: Ha.
                      move /eqP in Ha. subst s.
                      replace (sq a) with (sq a - 0). 
                      eapply UM_aux_ttqa_a with 
                      (a:=a)(a0:=s')(B:=B)(ta:=0)(tb:=0)(A:=A'). all:auto.
                      destruct (a_eqb s' a) eqn:Ha1. move /eqP in Ha1.
                      subst s'. destruct a. simpl in H2. lia.
                      move /eqP in Ha1. auto. 
                      replace (asks_of (replace_column 
                     (UM_aux B (a::A') 0 0) (uniform_price B (a::A')))) with
                     (asks_of (UM_aux B (a::A') 0 0)) in H3. auto.
                     apply replace_column_asks. lia.
                     move /eqP in Ha. 
                     eapply UM_aux_ttqb_fair_ask_t with (a1:=s)(a2:=s')
                     (a:=a)(B:=B)(A:=A')(ta:=0)(tb:=0) in H2.
                     apply H2. auto. auto. auto. auto. auto.
                     replace (asks_of (replace_column 
                     (UM_aux B (a::A') 0 0) (uniform_price B (a::A')))) with
                     (asks_of (UM_aux B (a::A') 0 0)) in H3.
                     eapply UM_aux_fair_ask_in. all:auto. eauto. auto.
                     apply H1. apply replace_column_asks.
                     replace (asks_of (replace_column 
                     (UM_aux B (a::A') 0 0) (uniform_price B (a::A')))) with
                     (asks_of (UM_aux B (a::A') 0 0)) in H3. auto.
                     apply replace_column_asks.
                     eapply replace_column_ttqa.
                    }
                  }
                 { unfold UM_matching. unfold fair_on_bids.
                   intros. split.
                   { replace (bids_of (replace_column 
                     (UM_aux B (A) 0 0) (uniform_price B (A)))) with
                     (bids_of (UM_aux B (A) 0 0)).
                      replace (bids_of (replace_column 
                     (UM_aux B (A) 0 0) (uniform_price B (A)))) with
                     (bids_of (UM_aux B (A) 0 0)) in H3. 
                     eapply UM_aux_fair_bid_in. all:auto. eauto. auto.
                     apply H1. apply replace_column_bids.
                     apply replace_column_bids. }
                   { replace (ttqb (replace_column 
                     (UM_aux B A 0 0) (uniform_price B A)) b) with
                     (ttqb (UM_aux B A 0 0) b). 
                      case B as [|b1 B']. simpl in H1. 
                      destruct H1. auto. destruct (b_eqb b1 b) eqn: Hb.
                      move /eqP in Hb. subst b.
                      replace (bq b1) with (bq b1 - 0). 
                      eapply UM_aux_ttqb_b with 
                      (b:=b1)(b0:=b')(B:=B')(ta:=0)(tb:=0)(A:=A). all:auto.
                      destruct (b_eqb b' b1) eqn:Hb1. move /eqP in Hb1.
                      subst b'. destruct b1. simpl in H2. lia.
                      move /eqP in Hb1. auto. 
                      replace (bids_of (replace_column 
                     (UM_aux (b1::B') (A) 0 0) (uniform_price (b1::B') (A)))) with
                     (bids_of (UM_aux (b1::B') (A) 0 0)) in H3. auto.
                     apply replace_column_bids. lia.
                     move /eqP in Hb. 
                     eapply UM_aux_ttqb_fair_bid_t with (b1:=b)(b2:=b')
                     (b:=b1)(B:=B')(A:=A)(ta:=0)(tb:=0) in H2.
                     apply H2. auto. auto. auto. auto. auto.
                      replace (bids_of (replace_column 
                     (UM_aux (b1::B') (A) 0 0) (uniform_price (b1::B') (A)))) with
                     (bids_of (UM_aux (b1::B') (A) 0 0)) in H3. 
                     eapply UM_aux_fair_bid_in. all:auto. eauto. auto.
                     apply H1. apply replace_column_bids.
                     replace (bids_of (replace_column 
                     (UM_aux (b1::B') (A) 0 0) (uniform_price (b1::B') (A)))) with
                     (bids_of (UM_aux (b1::B') (A) 0 0)) in H3. auto.
                     apply replace_column_bids.
                     eapply replace_column_ttqb.
                    }
                  }
               } Qed.
                   



(*Move this lemma into another file*)
Lemma exists_ttq_top (B:list Bid)(A:list Ask)(M:list fill_type)(b:Bid)(a:Ask)
(NZT: forall m : fill_type, In m M -> tq m > 0)
(NZA:(forall a0, In a0 (a::A) -> (sq a0) > 0))
(NZB:(forall b0, In b0 (b :: B) -> bq b0 > 0))
(Hanti: (antisymmetric by_sp)/\(antisymmetric by_dbp))
(NDA:NoDup (idas_of (a::A)))(NDB:NoDup (idbs_of (b::B))):
Sorted by_dbp (b::B) -> 
Sorted by_sp (a::A) -> 
(Is_uniform M (b::B) (a::A)) -> 
b>=a ->
QM(M)>=(min (bq b) (sq a)) -> 
(exists M', (Is_uniform M' (b::B) (a::A))/\
(ttqa M' a >= min (bq b) (sq a))/\(ttqb M' b >= min (bq b) (sq a))/\QM(M)=QM(M')/\
forall m : fill_type, In m M' -> tq m > 0).
Proof.   intros. set (M':=FAIR M (b::B) (a::A)).
         assert (matching_in (b :: B) (a :: A) M').
         apply idbs_of_nodup in NDB.
         apply idas_of_nodup in NDA. 
         apply FAIR_is_matching.
         all:auto. apply H1.
         assert (Is_IR M').
         apply FAIR_is_IR.
         all: auto. apply H1. apply H1.
         assert (Uniform M').
         apply FAIR_is_Uniform.
         all: auto. apply H1. apply H1.
         assert (QM M' = QM M). symmetry. apply FAIR_Quantity.
         all: auto. apply H1.
         exists M'. all:split;auto. split.  auto. all:split;auto.
         { apply FAIR_ttq. all:auto. apply H1. }
         split. 
         { apply FAIR_ttq. all:auto. apply H1. }
         split. auto. 
         { apply FAIR_NZT. all:auto. apply H1. } Qed.

Lemma exists_opt_k (B:list Bid)(A:list Ask)(b:Bid)(a:Ask):
(*(NZT: forall m : fill_type, In m M -> tq m > 0):*)
Sorted by_dbp (b::B) -> 
Sorted by_sp (a::A) -> 
(forall k M,
(Is_uniform M (b::B) (a::A)) -> 
b>=a ->
QM(M)>=(min (bq b) (sq a)) ->
(ttqa M a >= min (bq b) (sq a)) -> 
(ttqb M b >= min (bq b) (sq a)) ->
(min (bq b) (sq a) - ttq_ab M b a = k) ->
(forall m : fill_type, In m M -> tq m > 0) ->
(exists OPT, (Is_uniform OPT (b::B) (a::A))/\
(min (bq b) (sq a) - ttq_ab OPT b a = 0)/\QM(M)=QM(OPT)/\
forall m : fill_type, In m OPT -> tq m > 0)).
Proof. intros B0 A0 k.
       case (Nat.leb (bq b) (sq a)) eqn:Hab.
       { 
         assert (min (bq b) (sq a) = bq b). 
         eapply min_l. move /leP in Hab;lia. rewrite H. 
         induction k.
         { intros M H0 H1 H2 H3 H4 H5 NZT.  (*Base induction case*)
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
           { split. lia. auto. } 
         }
         { intros M H0 H1 H2 H3 H4 H5 NZT.  (*Main induction case*)
           assert(ttq_ab M b a < bq b). lia.
           assert(ttqb M b = (bq b)). 
           assert(HMb : ttqb M b <= bq b). 
           assert(In b (bids_of M) \/~In b (bids_of M)).
           eauto. destruct H7. 
           eapply H0. auto. apply ttqb_elim in H7. lia. lia.
           assert(exists m1, (In m1 M/\ (bid_of m1) = b /\(ask_of m1) <>a )).
           eapply b_in_a_out_m_exists with (M:=M)(a:=a)(b:=b). lia. lia.
           assert(exists m2, (In m2 M/\ (ask_of m2) = a /\(bid_of m2) <>b )).
           eapply a_in_b_out_m_exists with (M:=M)(a:=a)(b:=b). lia. lia.
           destruct H8 as [m1 H8]. destruct H9 as [m2 H9].
           assert(Hm1m2:m1<>m2).
            destruct H8. destruct H9.
            destruct H10. destruct H11. 
            assert(Hm1m2:m1 = m2 \/ m1 <> m2).
            eauto. destruct Hm1m2. subst m1. subst b. 
            elim H13.  auto. auto.
            set (M':=(g_increase_top M m1 m2 b a)).
            assert(HM'size: QM M = QM M').
            apply g_increase_top_size. auto.
            apply H8. apply H9. 
            auto.
            assert(Is_uniform M' (b :: B) (a :: A)
            /\QM M' >= bq b /\ttqa M' a >= bq b/\ttqb M' b >= bq b
            /\bq b - ttq_ab M' b a = k). split.
            apply g_increase_top_Is_Uniform.
            all:auto.
            apply H9. apply H8. symmetry. apply H8.
            symmetry. apply H9.
            destruct H9. destruct H10. auto. 
            destruct H8. destruct H10. auto. 
            split. lia. split. 
            replace (ttqa M' a) with (ttqa M a). lia.
            symmetry. eapply g_increase_top_sqa_equal.
            all: auto. apply H9. apply H8. symmetry;apply H9.
            split. 
            replace (ttqb M' b) with (ttqb M b). lia.
            symmetry. eapply g_increase_top_bqb_equal.
            all: auto. apply H9. apply H8. symmetry;apply H8.
            rewrite g_increase_top_trade_equal.
            auto. apply H9. apply H8. auto. symmetry;apply H9.
            destruct H9. destruct H10. auto. 
            symmetry;apply H8.
            destruct H8. destruct H10. auto. lia. 
            rewrite HM'size.
            eapply IHk with (M:=M'). destruct H10. auto. auto.
            lia.  all: try apply H10. apply g_increase_top_NZT. auto.
            apply H8. apply H9. 
          }
        }
        { (*Case -2 bq b >= sq*)
         
         assert (min (bq b) (sq a) = sq a).
         eapply min_r. move /leP in Hab;lia. rewrite H. 
         induction k.
         { intros M H0 H1 H2 H3 H4 H5 NZT.  (*Base induction case*)
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
           { split. lia. auto. } 
         }
         { intros M H0 H1 H2 H3 H4 H5 NZT.  (*Main induction case*)
           assert(ttq_ab M b a < sq a). lia.
           assert(ttqa M a = (sq a)).
           assert(HMa : ttqa M a <= sq a). 
           assert(In a (asks_of M) \/~In a (asks_of M)).
           eauto. destruct H7. 
           eapply H0. auto. apply ttqa_elim in H7. lia. lia.
           assert(exists m1, (In m1 M/\ (bid_of m1) = b /\(ask_of m1) <>a )).
           eapply b_in_a_out_m_exists with (M:=M)(a:=a)(b:=b). lia. lia.
           assert(exists m2, (In m2 M/\ (ask_of m2) = a /\(bid_of m2) <>b )).
           eapply a_in_b_out_m_exists with (M:=M)(a:=a)(b:=b). lia. lia.
            destruct H8 as [m1 H8]. destruct H9 as [m2 H9].
            assert(Hm1m2:m1<>m2).
            destruct H8. destruct H9.
            destruct H10. destruct H11. 
            assert(Hm1m2:m1 = m2 \/ m1 <> m2).
            eauto. destruct Hm1m2. subst m1. subst b. 
            elim H13.  auto. auto.
            set (M':=(g_increase_top M m1 m2 b a)).
            assert(HM'size: QM M = QM M').
            apply g_increase_top_size. auto.
            apply H8. apply H9. 
            auto.
            assert(Is_uniform M' (b :: B) (a :: A)/\
            QM M' >= sq a /\ttqa M' a >= sq a/\ttqb M' b >= sq a
            /\sq a - ttq_ab M' b a = k). split.
            apply g_increase_top_Is_Uniform.
            all:auto.
            apply H9. apply H8. symmetry. apply H8.
            symmetry. apply H9.
            destruct H9. destruct H10. auto. 
            destruct H8. destruct H10. auto. 
            split. lia. split. 
            replace (ttqa M' a) with (ttqa M a). lia.
            symmetry. eapply g_increase_top_sqa_equal.
            all: auto. apply H9. apply H8. symmetry;apply H9.
            split. 
            replace (ttqb M' b) with (ttqb M b). lia.
            symmetry. eapply g_increase_top_bqb_equal.
            all: auto. apply H9. apply H8. symmetry;apply H8.
            rewrite g_increase_top_trade_equal.
            auto. apply H9. apply H8. auto. symmetry;apply H9.
            destruct H9. destruct H10. auto. 
            symmetry;apply H8.
            destruct H8. destruct H10. auto. lia. 
            rewrite HM'size.
            eapply IHk with (M:=M'). destruct H10. auto. auto. 
            all: try apply H10. apply g_increase_top_NZT. auto.
            apply H8. apply H9. 
          }
        } Qed.

Lemma exists_opt (B:list Bid)(A:list Ask)(M:list fill_type)(b:Bid)(a:Ask)
(NZT: forall m : fill_type, In m M -> tq m > 0)
(NZA:(forall a0, In a0 (a::A) -> (sq a0) > 0))
(NZB:(forall b0, In b0 (b :: B) -> bq b0 > 0))
(Hanti: (antisymmetric by_sp)/\(antisymmetric by_dbp))
(NDA:NoDup (idas_of (a::A)))(NDB:NoDup (idbs_of (b::B))):
Sorted by_dbp (b::B) -> 
Sorted by_sp (a::A) -> 
(Is_uniform M (b::B) (a::A)) -> 
b>=a ->
QM(M)>=(min (bq b) (sq a)) ->
(exists OPT, (Is_uniform OPT (b::B) (a::A))/\
(ttq_ab OPT b a = min (bq b) (sq a))/\QM(M)=QM(OPT)/\
(forall m : fill_type, In m OPT -> tq m > 0)).
Proof. intros. 
       assert((exists M', (Is_uniform M' (b::B) (a::A))/\
       (ttqa M' a >= min (bq b) (sq a))/\
       (ttqb M' b >= min (bq b) (sq a))/\QM(M)=QM(M')
       /\forall m : fill_type, In m M' -> tq m > 0)).
       eapply exists_ttq_top. all:auto. destruct H4 as [M0 H5].
       destruct H5. destruct H5. destruct H6. 
       destruct (Nat.min (bq b) (sq a) - ttq_ab M0 b a) eqn:Hk.
       {
         eapply exists_opt_k with (k:=0)(A:=A)(a:=a)(B:=B)(b:=b) in H5.
         destruct H5 as [OPT H5]. exists OPT. 
         destruct H5. destruct H7.
         split. apply H5. split. 
         assert (Hmin:ttq_ab OPT b a <= Nat.min (bq b) (sq a)).
         eapply matching_in_elim9 with (B:=(b::B))(A:=(a::A)).
         apply H5.  all:auto.  lia. split. lia. apply H8. lia. apply H7.
       }  
       { assert(Haba:ttqa M0 a >=ttq_ab M0 b a).
         eauto. 
         eapply exists_opt_k with (k:= S n)(A:=A)(a:=a)(B:=B)(b:=b) in H5.
         destruct H5 as [OPT H5]. exists OPT. 
         destruct H5. destruct H7.
         split. apply H5. split. 
         assert (Hmin:ttq_ab OPT b a <= Nat.min (bq b) (sq a)).
         eapply matching_in_elim9 with (B:=(b::B))(A:=(a::A)).
         apply H5.  all:auto.  lia. split. lia. apply H8. lia. apply H7.       }
Qed. 


Lemma matching_on_nilA (B:list Bid) (M:list fill_type) : matching_in B nil M -> M=nil.
Proof. { intros H1. unfold matching_in in H1. destruct H1 as [H1 H2].
         destruct H2 as [H2 H3]. unfold matching in H1. destruct H1 as [H1 H4]. 
         unfold All_matchable in H1. assert (HAMnil: (asks_of M) = nil). eauto.
         case M eqn: HM. auto. simpl in HAMnil. inversion HAMnil. } Qed.

Lemma matching_on_nilB (A: list Ask)(M:list fill_type) : matching_in nil A M -> M=nil.
Proof. { intros H1. unfold matching_in in H1. destruct H1 as [H1 H2].
         destruct H2 as [H2 H3]. unfold matching in H1. destruct H1 as [H1 H4]. 
         unfold All_matchable in H1. assert (HBMnil: (bids_of M) = nil). eauto.
         case M eqn: HM. auto. simpl in HBMnil. inversion HBMnil. } Qed.

Lemma matching_on_bnill (A: list Ask)(M:list fill_type)(b:Bid): 
matching_in (b::nil) A M -> QM(M)<=bq b.
Proof. intros. destruct H. destruct H. destruct H0.
       assert(NoDup (b :: nil)). eauto. apply QM_equal_QMb in H0. 
       simpl in H0. 
       apply fill_size_vs_bid_size with (M:=M) in H3.
       simpl in H3. lia. intros. 
       assert(In b0 (bids_of M)\/~In b0 (bids_of M)).
       eauto. destruct H5. apply H1. auto. apply ttqb_elim in H5. lia.
       eauto. Qed.
       
Lemma matching_on_anill (B: list Bid)(M:list fill_type)(a:Ask): 
matching_in B (a::nil) M -> QM(M)<=sq a.
Proof. intros. destruct H. destruct H. destruct H0.
       assert(NoDup (a :: nil)). eauto. apply QM_equal_QMa in H2. 
       simpl in H2. 
       apply fill_size_vs_ask_size with (M:=M) in H3.
       simpl in H3. lia. intros. 
       assert(In a0 (asks_of M)\/~In a0 (asks_of M)).
       eauto. destruct H5. apply H1. auto. apply ttqa_elim in H5. lia.
       eauto. Qed.



Lemma unmatchableAB_nil (B:list Bid) (A:list Ask) (b:Bid)(a:Ask)
(M:list fill_type): Sorted by_dbp (b::B) -> Sorted by_sp (a::A) ->
matching_in (b::B) (a::A) M -> b<a-> M=nil.
Proof. { intros H1 H2 H3 H4.
         case M as [|f  M'] eqn:HM.
         { auto. }
         { set (b0:= bid_of f). set (a0:= ask_of f).
           assert (Hfask: In (ask_of f) (a::A)). 
           { eapply matching_in_elim5. exact H3. }
           assert (Hfbid: In (bid_of f) (b::B)). 
           { eapply matching_in_elim4.  exact H3. }
           assert (Hmatch: bid_of f >= ask_of f). eauto.
           assert (h1: by_dbp b b0). 
           { unfold b0. unfold is_true. apply bool_fun_equal.
             intro. exact is_true_true. intro.
              eapply Sorted_elim2. exact by_dbp_refl.
            exact H1. exact Hfbid. }
           assert (h2: by_sp a a0).
           { apply Sorted_elim2 with (x:=a0) in H2.
             auto. apply by_sp_refl. eauto.
           }
           unfold by_dbp in h1. 
           move /orP in h1.
           unfold by_sp in h2. 
           move /orP in h2.
           destruct h1;destruct h2. 
           {
           move /leP in H.
           move /leP in H0.
           unfold b0 in H.
           unfold a0 in H0.
           lia.
           }
           {
           move /leP in H.
           move /andP in H0. destruct H0.
           move /eqP in H0.
           unfold b0 in H.
           unfold a0 in H0.
           lia.
           }
           {
           move /leP in H0.
           move /andP in H. destruct H.
           move /eqP in H.
           unfold b0 in H.
           unfold a0 in H0.
           lia.
           }
           {
           move /andP in H. destruct H.
           move /eqP in H.
           move /andP in H0. destruct H0.
           move /eqP in H0. 
           unfold b0 in H.
           unfold a0 in H0.
           lia.
           }            
 } } Qed.

Theorem UM_aux_OPT (B:list Bid)(A:list Ask)(M:list fill_type)
(b:Bid)(a:Ask)(ta tb: nat)
(NDA:NoDup (ida a::(idas_of A)))(NDB:NoDup (idb b::(idbs_of B)))
(NZT: forall m : fill_type, In m M -> tq m > 0)
(NZB: forall b0, In b0 ((Mk_bid (bp b) (btime b) (bq b - tb) (idb b))::B) -> (bq b0)>0)
(NZA: forall a0, In a0 ((Mk_ask (sp a) (stime a) (sq a - ta) (ida a))::A) -> (sq a0)>0)
(Hanti: (antisymmetric by_sp)/\(antisymmetric by_dbp)):
Sorted by_dbp (b::B) -> 
Sorted by_sp (a::A) -> 
(Is_uniform M ((Mk_bid (bp b) (btime b) (bq b - tb) (idb b))::B)
                        ((Mk_ask (sp a) (stime a) (sq a - ta) (ida a))::A))
-> QM(M) <= QM(UM_aux (b::B) (a::A) tb ta).
Proof. intros. 
assert(HBS: Sorted by_dbp ((Mk_bid (bp b) (btime b) (bq b - tb) (idb b))::B)).
constructor. eauto. intros. 
eapply Sorted_elim4 with (x0:=x) in H.
destruct b;destruct x. auto. auto.
assert(HAS: Sorted by_sp ((Mk_ask (sp a) (stime a) (sq a - ta) (ida a))::A)).
constructor. eauto. intros. 
eapply Sorted_elim4 with (x0:=x) in H0.
destruct a;destruct x. auto. auto.
funelim (UM_aux (b::B) (a::A) tb ta).
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
    eapply exists_opt in H4.
    all:auto. 
    destruct H4 as [M0 H4].
    destruct H4. destruct H5. destruct H6 as [H6 HNZT]. rewrite H6.
    destruct (Nat.eqb (bq b - tb) (sq a - ta)) eqn: Hqabeq.
    {
      simpl. simpl in H5.
      assert(HM0':exists M0', (Is_uniform M0' l l0)/\(QM(M0)=QM(M0') + (bq b - tb))/\
      (forall m : fill_type, In m M0' -> tq m > 0)).
      {
        eapply exists_M0_reduced_bid_ask_uniform in H4.
        {
          destruct H4 as [M1 H4]. exists M1.
          destruct H4 as [H4 H7].
          destruct H7 as [H7 NZTM0]. simpl in H7. auto. 
        }
        { auto. }
        split.
        { rewrite H5.  
          move /eqP in Hqabeq. simpl. lia.
        }
        { move /eqP in Hqabeq. simpl. lia. }
      }
      destruct HM0' as [M0' HM0'].
      replace (QM M0) with (QM M0' + (bq b - tb)).
      cut(QM M0' <= QM (UM_aux l l0 0 0)). lia.
      case l eqn: Hl.
      { simp UM_aux.
        simpl.  
        { destruct HM0'. 
          destruct H7. destruct H9. 
          apply matching_on_nilB in H9. 
          rewrite H9.  simpl. lia. }
      }
      {
      case l0 eqn: Hl0.
        { simp UM_aux.
          simpl. destruct HM0'. 
          destruct H7. destruct H9. 
          apply matching_on_nilA in H9. 
          rewrite H9.  simpl. lia.
        }
        {
          eapply H with (M:=M0'). all:auto.
          { eauto. } {eauto. } 
          { apply HM0'. } 
          { intros.
            destruct H7. subst b1. simpl. 
            replace (bq b0 - 0) with (bq b0). eauto.
            lia. eauto. }
          { intros.
            destruct H7. subst a1. simpl. 
            replace (sq a0 - 0) with (sq a0). eauto.
            lia. eauto. }          
          { eauto. } 
          { eauto. }
          { replace (bq b0 - 0) with (bq b0).
            replace (sq a0 - 0) with (sq a0).
            destruct HM0'. destruct b0;destruct a0. intros. 
            eapply H7.  lia. lia.
          }  
          { replace (bq b0 - 0) with (bq b0).
            assert(Sorted by_dbp (b0 :: l1));eauto;destruct b0;auto.
            lia.
          }
          { replace (sq a0 - 0) with (sq a0).
            assert(Sorted by_sp (a0 :: l2));eauto;destruct a0;auto.
            lia. 
          }
        }
     } 
     destruct HM0'. destruct H8;auto.
    }
    {
      destruct (Nat.leb (bq b - tb) (sq a - ta)) eqn:Hle.
      {
        simpl. simpl in H5.
        case l eqn: Hl.
        { simp UM_aux.
          simpl. destruct H4. destruct H7.
          apply matching_on_bnill in H7.
          simpl in H7. lia.
        }
        {
          assert(HM0':exists M0', (Is_uniform M0' 
          ((Mk_bid (bp b0) (btime b0) (bq b0 - 0) (idb b0))::l1) 
          ((Mk_ask (sp a) (stime a) (sq a - (ta + (bq b - tb))) (ida a))::l0))
          /\(QM(M0)=QM(M0') + (bq b - tb))/\
          (forall m : fill_type, In m M0' -> tq m > 0)).
       {
         eapply exists_M0_reduced_ask_uniform with (b:=
         {|
          bp := b;
          btime := btime b;
          bq := bq b - tb;
          idb := idb b |}) in H4.
         {
         destruct H4 as [M1 H4]. exists M1.
         destruct H4. simpl in H4. 
         replace (sq a - (ta + (bq b - tb))) with (sq a - ta - (bq b - tb)).
         split. replace (bq b0 - 0) with (bq b0). 
         replace ({| bp := b0; btime := btime b0; bq := bq b0; idb := idb b0 |})
         with b0. eapply H4. destruct b0. simpl. auto.
         lia. simpl in H7. auto. lia. }
         simpl. eauto. auto.
         simpl. rewrite H5.  
         move /leP in Hle. lia. 
         move /eqP in Hqabeq. move /leP in Hle. 
         simpl. lia.
        }
          destruct HM0' as [M0' HM0'].
          replace (QM M0) with (QM M0' + (bq b - tb)).
          cut(QM M0' <= QM (UM_aux (b0 :: l1) (a :: l0) 0 (ta + (bq b - tb)))).
          lia.
          eapply H0 with (M:=M0'). all:auto.
          { eauto. } 
          { apply HM0'. }
          { move /leP in Hle. intros.
            destruct H7. subst b1. simpl.
            replace (bq b0 - 0) with (bq b0). eauto.
            lia. eauto.
          }
          { move /leP in Hle. intros.
            destruct H7. subst a0. simpl. move /eqP in Hqabeq. lia. eauto. }
          { eauto. }
          { destruct HM0'.  
            eapply H7.
          }  
          { replace (bq b0 - 0) with (bq b0). destruct b0;auto. eauto. 
            lia.
          } 
          { constructor. eauto. intros. simpl. 
            eapply Sorted_elim4 with (x0:=x) in H3.
            destruct a;destruct x. unfold by_sp. simpl.
            unfold by_sp in H3. simpl in H3. auto. auto.
          }
          { 
          destruct HM0'. destruct H8;auto.
          }
      }
    }
    {
       simpl. simpl in H5.
       case l0 eqn: Hl0. 
       { simp UM_aux.
         simpl. destruct H4. destruct H7.
         apply matching_on_anill in H7.
         simpl in H7. lia.
       }
       assert(HM0':exists M0', (Is_uniform M0' 
       ((Mk_bid (bp b) (btime b) (bq b - (tb + (sq a - ta))) (idb b))::l)
       ((Mk_ask (sp a0) (stime a0) (sq a0 - 0) (ida a0))::l1))
       /\(QM(M0)=QM(M0') + (sq a - ta))/\
       (forall m : fill_type, In m M0' -> tq m > 0)).
       {
         eapply exists_M0_reduced_bid_uniform with (a:=
         {|
          sp := a;
          stime := stime a;
          sq := sq a - ta;
          ida := ida a |}) in H4.
         {
         destruct H4 as [M1 H4]. exists M1.
         destruct H4. simpl in H4. 
         replace (bq b - (tb + (sq a - ta))) with (bq b - tb - (sq a - ta)).
         split. replace (sq a0 - 0) with (sq a0). 
         replace ({| sp := a0; stime := stime a0; sq := sq a0; ida := ida a0 |})
         with a0. eapply H4. destruct a0. simpl. auto.
         lia. simpl in H7. auto. lia. }
         simpl. eauto. auto.
         simpl. rewrite H5.  
         move /leP in Hle. lia. 
         move /eqP in Hqabeq. move /leP in Hle. 
         simpl. lia.
        }
      destruct HM0' as [M0' HM0'].
      replace (QM M0) with (QM M0' + (sq a - ta)).
      cut(QM M0' <= QM (UM_aux (b :: l) (a0 :: l1) (tb + (sq a - ta)) 0)).
      lia.
      eapply H1 with (M:=M0'). all:auto.
      { eauto. } 
      { apply HM0'. }
      { move /leP in Hle. intros.
            destruct H7. subst b0. simpl.
            move /eqP in Hqabeq. lia. eauto.
      }
      { move /leP in Hle. intros.
        destruct H7. subst a1. simpl. 
        replace (sq a0 - 0) with (sq a0). eauto. 
        lia. eauto.
      }
      { eauto. }
      { destruct HM0'. 
        eapply H7.
      }  
      { constructor. eauto. intros. simpl. 
        eapply Sorted_elim4 with (x0:=x) in H2.
        destruct b;destruct x. unfold by_sp. simpl.
        unfold by_sp in H2. simpl in H2. auto. auto.
      }
      {
      replace (sq a0 - 0) with (sq a0). destruct a0;auto. eauto. 
      lia.
      }
      {
      destruct HM0'. destruct H8;auto.
      }
      
    }
   } 
   { simpl. move /leP in Hqab;lia. }
   }
  }
assert(Hnil:M=nil).
destruct H4. destruct H5.
apply unmatchableAB_nil in H5.
auto.
               { constructor. eauto. intros. simpl. 
        eapply Sorted_elim4 with (x0:=x) in H2.
        destruct b;destruct x. unfold by_sp. simpl.
        unfold by_sp in H2. simpl in H2. auto. auto.
      }
       { constructor. eauto. intros. simpl. 
            eapply Sorted_elim4 with (x0:=x) in H3.
            destruct a;destruct x. unfold by_sp. simpl.
            unfold by_sp in H3. simpl in H3. auto. auto.
          }
          simpl. move /leP in Hab. lia.
 rewrite Hnil. simpl. lia.
Qed.


Theorem UM_aux_optimal (B:list Bid)(A:list Ask)(M:list fill_type)
(NZB: forall b, In b B -> (bq b)>0)
(NZA: forall a, In a A -> (sq a)>0)
(NDA:NoDup (idas_of A))
(NDB:NoDup (idbs_of B))
(NZT: forall m : fill_type, In m M -> tq m > 0)
(Hanti: (antisymmetric by_sp)/\(antisymmetric by_dbp)):
Sorted by_dbp B -> 
Sorted by_sp A ->
(Is_uniform M B A)
-> QM(M) <= QM(UM_aux B A 0 0).
Proof. intros. case B as [|b B']. 
       {
        simp UM_aux.
        simpl. destruct H1. 
        destruct H2.
        apply matching_on_nilB in H2. 
        rewrite H2.  simpl. lia.
        }
       case A as [|a A'].
       {
        simp UM_aux.
        simpl. destruct H1. 
        destruct H2.
        apply matching_on_nilA in H2. 
        rewrite H2.  simpl. lia.
       }        
       apply UM_aux_OPT.
       all:auto.
       { intros. destruct H2. subst b0. simpl.
        replace (bq b - 0) with (bq b). eauto. lia. eauto.
       }
       { intros. destruct H2. subst a0. simpl.
        replace (sq a - 0) with (sq a). eauto. lia. eauto.
       }
       { replace (bq b - 0) with (bq b).
         replace (sq a - 0) with (sq a).
         destruct b. destruct a. simpl. auto.
         lia. lia.
       }
Qed.  

End UM.
