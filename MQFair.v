
(* ------------   Work to be done : organise the hints properly ------------- *)



(* -------------------------------------------------------------------------------------

      This file contains all the important results about fair matching.
      The main result is existance of a fair matching without compromize of it's size.

       by_sp            <===>   order by increasing sp and time
       by_dbp           <===>   order by decreasing bp and increasing time (if bp is same)
       FOA M A          <===>   makes M fair on asks A
       FOB M B          <===>   makes M fair on bids B


Some important results:

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
Require Export mFair_Bid.
Require Export mFair_Ask.

(*Require Export AuctionInvar.*)

Section Fair.

Definition Is_fair (M: list fill_type) (B: list Bid) (A: list Ask) 
  :=  fair_on_asks M A /\ fair_on_bids M B.

Definition FAIR (M: list fill_type) (B: list Bid) (A: list Ask) :=
FOB (sort m_dbp (FOA (sort m_sp M) (sort by_sp A))) (sort by_dbp B).


(*##############These lemmas of FAIR are needed in UM and MM proofs.####################*)

Lemma FOA_aux_ttqa_QM (M: list fill_type)(A: list Ask)(a:Ask)(t:nat)
(NZT:(forall m, In m M -> (tq m) > 0) )(NDA:NoDup (a::A)):
QM(M)<=(sq a) - t -> ttqa (FOA_aux M (a::A) t) a = QM(M).
Proof. 
revert t A a NDA. induction M as [ | m M']. intros.
simp FOA_aux. simpl. simpl in H. lia.
{ intros. simp FOA_aux. destruct (Nat.eqb (tq m) (sq a -t )) eqn: Heq0. 
{ 
simpl.  assert(a_eqb a a = true). eauto. rewrite H0.
simpl in H. move /eqP in Heq0.
cut (ttqa (FOA_aux M' A 0) a = 0). lia.
assert (~In a A). eauto.
 assert (forall t, asks_of (FOA_aux M' A t) [<=] A). intros.
  eapply FOA_aux_asks_subset with (M:=M')(t:=t0)(A:=A).
 assert (forall t, ~In a (asks_of (FOA_aux M' A t))).  intros. specialize (H2 t0).
 eauto. apply ttqa_elim. auto. }
{ intros. destruct (Nat.leb (tq m) (sq a - t)) eqn: Hle. 
{ simpl. assert(a_eqb a a = true). eauto. rewrite H0. rewrite IHM'.
auto. auto. simpl in H. lia. lia. }
{ simpl. 
assert(a_eqb a a = true). eauto. rewrite H0. simpl in H. move /leP in Hle. 
cut (ttqa (FOA_aux ({|bid_of := bid_of m;
      ask_of := ask_of m;
      tq := tq m - (sq a - t);
      tp := tp m |} :: M') A 0) a = 0). lia.
assert (~In a A). eauto.
 assert (asks_of (FOA_aux ({|bid_of := bid_of m;
      ask_of := ask_of m;
      tq := tq m - (sq a - t);
      tp := tp m |} :: M') A 0) [<=] A). eapply FOA_aux_asks_subset.
 assert (~In a (asks_of (FOA_aux ({|bid_of := bid_of m;
      ask_of := ask_of m;
      tq := tq m - (sq a - t);
      tp := tp m |} :: M') A 0))).  
 eauto. apply ttqa_elim. auto. }} } Qed.

Lemma FOA_ttqa_QM (M: list fill_type)(A: list Ask)(a:Ask)
(NZT:(forall m, In m M -> (tq m) > 0) )(NDA:NoDup (a::A)):
QM(M)<=(sq a) -> ttqa (FOA M (a::A)) a = QM(M).
Proof. intros. apply FOA_aux_ttqa_QM with (t:=0). auto. auto. lia. Qed.






Lemma FOB_aux_ttqb_QM (M: list fill_type)(B: list Bid)(b:Bid)(t:nat)
(NZT:(forall m, In m M -> (tq m) > 0) )(NDB:NoDup (b::B)):
QM(M)<=(bq b) - t -> ttqb (FOB_aux M (b::B) t) b = QM(M).
Proof. 
revert t B b NDB. induction M as [ | m M']. intros.
simp FOB_aux. simpl. simpl in H. lia.
{ intros. simp FOB_aux. destruct (Nat.eqb (tq m) (bq b -t )) eqn: Heq0. 
{ 
simpl.  assert(b_eqb b b = true). eauto. rewrite H0.
simpl in H. move /eqP in Heq0.
cut (ttqb (FOB_aux M' B 0) b = 0). lia.
assert (~In b B). eauto.
 assert (forall t, bids_of (FOB_aux M' B t) [<=] B). intros.
  eapply FOB_aux_bids_subset with (M:=M')(t:=t0)(B:=B).
 assert (forall t, ~In b (bids_of (FOB_aux M' B t))).  intros. specialize (H2 t0).
 eauto. apply ttqb_elim. auto. }
{ intros. destruct (Nat.leb (tq m) (bq b - t)) eqn: Hle. 
{ simpl. 
assert(b_eqb b b = true). eauto. rewrite H0. rewrite IHM'. 
auto. auto. simpl in H. lia. lia. }
{ simpl. assert(b_eqb b b = true). eauto. rewrite H0. simpl in H. move /leP in Hle. 
cut (ttqb (FOB_aux ({|
     bid_of := bid_of m;
      ask_of := ask_of m;
      tq := tq m - (bq b - t);
      tp := tp m |} :: M') B 0) b = 0). lia.
assert (~In b B). eauto.
 assert (bids_of (FOB_aux ({|
      bid_of := bid_of m;
      ask_of := ask_of m;
      tq := tq m - (bq b - t);
      tp := tp m |} :: M') B 0) [<=] B). eapply FOB_aux_bids_subset.
 assert (~In b (bids_of (FOB_aux ({|
      bid_of := bid_of m;
      ask_of := ask_of m;
      tq := tq m - (bq b - t);
      tp := tp m |} :: M') B 0))).  
 eauto. apply ttqb_elim. auto. }
 } } Qed.

Lemma FOB_ttqb_QM (M: list fill_type)(B: list Bid)(b:Bid)
(NZT:(forall m, In m M -> (tq m) > 0) )(NDB:NoDup (b::B)):
QM(M)<=(bq b) -> ttqb (FOB M (b::B)) b = QM(M).
Proof. intros. apply FOB_aux_ttqb_QM with (t:=0). auto. auto. lia. Qed.



Lemma FAIR_ttq (M: list fill_type)(B: list Bid)(A:list Ask)
(a:Ask)(b:Bid)(NDB: NoDup (b::B))(NDA: NoDup (a::A))
(NZT:(forall m, In m M -> (tq m) > 0))
(NZA:(forall a0, In a0 (a::A) -> (sq a0) > 0))
(Hanti: (antisymmetric by_sp)/\(antisymmetric by_dbp) ):
Sorted by_dbp (b::B) -> 
Sorted by_sp (a::A) -> 
(matching_in (b::B) (a::A) M) ->
QM M >= Nat.min (bq b) (sq a)-> 
ttqa (FAIR M (b::B) (a::A)) a >= Nat.min (bq b) (sq a)/\
ttqb (FAIR M (b::B) (a::A)) b >= Nat.min (bq b) (sq a).
Proof. { intros H H0 HM HQ. unfold FAIR. 
       assert(HA:(sort by_sp (a::A)) = a::A).
       { 
        apply sort_equal_nodup. apply by_sp_refl. apply Hanti.
        all: auto. 
       }
       assert(HB:(sort by_dbp (b::B))  = b::B).
       {
        apply sort_equal_nodup. apply by_dbp_refl. apply Hanti.
        all: auto.
       }
       rewrite HA. rewrite HB.
       assert(HQ1:QM((sort m_sp M)) = QM((FOA (sort m_sp M) (a :: A)))).
       {
        apply FOA_size with (M:=(sort m_sp M))(A:=(a::A))(B:=(b::B)).
        all:auto. eauto. 
        apply match_inv with (M':= (sort m_sp M))(A':=a::A)(B':=b::B) in HM.
        auto. eauto. eauto. eauto.
       }
       assert(HQ3: QM (sort m_dbp (FOA (sort m_sp M) (a :: A))) = 
       QM ((FOA (sort m_sp M) (a :: A)))).
       {
        apply QM_perm. eauto.
       }
       assert(QM(M) = QM((sort m_sp M))).
       { apply QM_perm. eauto. }
       assert(HQB:QMb M (b :: B) <= QB (b :: B)).
       { 
        apply fill_size_vs_bid_size with (B:=(b :: B))(M:=M).
        all:auto. intros.
        assert(Hb0:(In b0 (bids_of M))\/~In b0 (bids_of M)). 
        eauto. destruct Hb0 as [Hb01 | Hb02]. apply HM.
        auto. apply ttqb_elim in Hb02. lia.
       }
       assert(HQA:QMa M (a :: A) <= QA (a :: A)).
       {
        apply fill_size_vs_ask_size with (A:=(a :: A))(M:=M).
        all:auto. intros.
        assert(Ha0:(In a0 (asks_of M))\/~In a0 (asks_of M)). 
        eauto. destruct Ha0 as [Ha01 | Ha02]. apply HM.
        auto. apply ttqa_elim in Ha02. lia.
       }
       assert(HQMb:QM M = QMb M (b :: B)). 
       {
        rewrite <- QM_equal_QMb with (M:=M)(B:=b::B). 
        all: auto.  apply HM.
       }
       assert(HQMa:QM M = QMa M (a :: A)).
       { 
        rewrite <- QM_equal_QMa with (M:=M)(A:=a::A). 
        all: auto.  apply HM.
       }
       (* Now doing for ttqa*)
       split.
       {
         assert(Hqa:ttqa (FOB (sort m_dbp (FOA (sort m_sp M) (a :: A))) (b :: B)) a = 
         ttqa ((sort m_dbp (FOA (sort m_sp M) (a :: A)))) a). 
         { 
          symmetry.
          apply FOB_asks_invariant. intros. 
          eapply FOA_NZT with (M:=(sort m_sp M))(A:=a::A).
          eauto. all:auto. eauto.
          rewrite HQ3. rewrite <- HQ1. rewrite <- H1.
          simpl. simpl in HQB. simpl in HQMb. lia.
         }
         rewrite Hqa. 
         assert(ttqa (sort m_dbp (FOA (sort m_sp M) (a :: A))) a = 
         ttqa ((FOA (sort m_sp M) (a :: A))) a).
         { 
          apply ttqa_of_perm. eauto. 
         }
         rewrite H2.
         assert(Nat.min (bq b) (sq a) = bq b \/Nat.min (bq b) (sq a) = sq a).
         lia. destruct H3.
         { destruct (Nat.leb (QM(M)) (sq a)) eqn: HQb.
           { move /leP in HQb.
             assert(ttqa (FOA (sort m_sp M) (a :: A)) a = QM((sort m_sp M))).
             apply FOA_ttqa_QM. all: auto. eauto. lia. lia.
           }
           { assert(ttqa (FOA (sort m_sp M) (a :: A)) a = sq a).
             apply FOA_aux_top_ask_fair0. all:auto. eauto. move /leP in HQb. lia. lia.
           }
         }
         {
          assert(ttqa (FOA (sort m_sp M) (a :: A)) a = sq a).
          apply FOA_aux_top_ask_fair0. all:auto. eauto. lia. lia.
         } 
      }
             (* Now doing for ttqa*)
      {
         assert(Nat.min (bq b) (sq a) = bq b \/Nat.min (bq b) (sq a) = sq a).
         lia. destruct H2.
         { 
           rewrite H2.
         assert(Hqb:ttqb (FOB (sort m_dbp (FOA (sort m_sp M) (a :: A))) (b :: B)) b = 
         bq b). 
         { 
          eapply FOB_aux_top_bid_fair0. all:auto. intros. 
          eapply FOA_NZT with (M:=(sort m_sp M))(A:=a::A).
          eauto. all:auto. eauto. lia. 
         }
         lia.
       }
        {
           destruct (Nat.leb (QM(M)) (bq b)) eqn: HQb.
           { move /leP in HQb.
             assert(ttqb (FOB (sort m_dbp (FOA (sort m_sp M) (a :: A))) (b :: B)) b
              = QM((sort m_dbp (FOA (sort m_sp M) (a :: A))))).
             apply FOB_ttqb_QM. all: auto. intros. 
             eapply FOA_NZT with (M:=(sort m_sp M))(A:=a::A).
             eauto. all:auto. eauto.
              lia. lia.
           }
           { assert(ttqb (FOB (sort m_dbp (FOA (sort m_sp M) (a :: A))) (b :: B)) b = bq b).
             apply FOB_aux_top_bid_fair0. all:auto. intros. 
             eapply FOA_NZT with (M:=(sort m_sp M))(A:=a::A).
             eauto. all:auto. eauto. move /leP in HQb. lia. lia. 
           } } }}      
       Qed.

Lemma FAIR_NZT (M: list fill_type)(B: list Bid)(A:list Ask)
(a:Ask)(b:Bid)(NDB: NoDup (b::B))(NDA: NoDup (a::A))
(NZT:(forall m, In m M -> (tq m) > 0))
(NZA:(forall a0, In a0 (a::A) -> (sq a0) > 0))
(NZB:(forall b0, In b0 (b :: B) -> bq b0 > 0))
(Hanti: (antisymmetric by_sp)/\(antisymmetric by_dbp) ):
Sorted by_dbp (b::B) -> 
Sorted by_sp (a::A) -> 
(matching_in (b::B) (a::A) M) ->
QM M >= Nat.min (bq b) (sq a)-> 
(forall m, In m (FAIR M (b::B) (a::A)) -> (tq m) > 0).
Proof. unfold FAIR. intros.  
eapply FOB_NZT with 
(M:=(sort m_dbp (FOA (sort m_sp M) (sort by_sp (a :: A)))))
(B:=(sort by_dbp (b :: B))).
intros. 
eapply FOA_NZT with (M:=(sort m_sp M))(A:=(sort by_sp (a :: A))).
eauto. all:auto. eauto.
eauto. all:auto. eauto. Qed.



Theorem FAIR_is_matching (M: list fill_type)(B: list Bid)(A:list Ask)(NDB: NoDup B)(NDA: NoDup A)
(NZT:(forall m, In m M -> (tq m) > 0))
(NZA:(forall a0, In a0 A -> (sq a0) > 0))
(Hanti: (antisymmetric by_sp)/\(antisymmetric by_dbp) ): 
matching_in B A M-> matching_in B A (FAIR M B A).
Proof. intros. unfold FAIR. apply FOB_matching.
       eauto. eauto. apply FOA_NZT. eauto. eauto. eauto.
       apply Hanti. apply FOA_matching.
       eauto. eauto. auto.
       apply Hanti. auto. Qed.


Lemma FAIR_is_IR (M: list fill_type)(B: list Bid)(A:list Ask)(NDB: NoDup B)(NDA: NoDup A)
(NZT:(forall m, In m M -> (tq m) > 0))
(NZA:(forall a0, In a0 A -> (sq a0) > 0))
(Hanti: (antisymmetric by_sp)/\(antisymmetric by_dbp) ): 
Is_IR M -> matching_in B A M-> Is_IR (FAIR M B A).
Proof. intros. unfold FAIR. 
       set(M0:=(sort m_dbp (FOA (sort m_sp M) (sort by_sp A)))).
       assert(M0match':matching_in B A (FOA (sort m_sp M) (sort by_sp A))).
       {
          eapply FOA_matching in H0. all:auto. apply Hanti. }
          assert(M0match:matching_in B A M0).
          {
          eapply match_inv with (A':=A) (M':=M0)(B':=B) in M0match'. auto.
          subst M0. eauto. auto. auto. 
       }
       assert(Is_IR M0).
       {
       unfold Is_IR. intros. assert(In m (FOA (sort m_sp M) (sort by_sp A))).
       eauto. apply FOA_IR with (M:=(sort m_sp M))(A:= (sort by_sp A)) in H2. auto.
         { eauto. }
         {eauto. }
         { apply Hanti. }
         { apply sort_correct. apply by_sp_P. apply by_sp_P. }
         { apply sort_correct. apply m_sp_P. apply m_sp_P. }
         { unfold Is_IR. intros. eauto. } 
         { assert (asks_of M [<=] A). apply H0. eauto. }
         { intros. assert(ttqa (sort m_sp M) a0 = ttqa M a0).
           apply ttqa_of_perm. auto. rewrite H3. 
           assert(In a0 (asks_of M)\/~In a0 (asks_of M)). eauto.
           destruct H4. apply H0. auto. apply ttqa_elim in H4. lia.
         } 
       }
       apply FOB_IR. 
       { (*NZT*) intros. assert(In m (FOA (sort m_sp M) (sort by_sp A))).
                eauto. eapply FOA_NZT with (M:=(sort m_sp M))(A:=(sort by_sp A)).
                eauto. eauto.  eauto. auto.
       }
       { eauto. }
       { apply Hanti. }
       { apply sort_correct. apply by_dbp_P. apply by_dbp_P. }
       { apply sort_correct. apply m_dbp_P. apply m_dbp_P. }
       { auto. }
       { assert(bids_of M0 [<=] B). apply M0match. eauto. }
       { intros. assert(In b0 (bids_of M0)\/~In b0 (bids_of M0)). eauto.
         destruct H2. apply M0match. auto. apply ttqb_elim in H2. lia.
       }
 Qed.

Lemma FAIR_is_Uniform (M: list fill_type)(B: list Bid)(A:list Ask)
(NDB: NoDup B)(NDA: NoDup A): 
Uniform M -> matching_in B A M-> Uniform (FAIR M B A).
Proof. unfold Uniform. intros. unfold FAIR.
assert(Uniform (FOA (sort m_sp M) (sort by_sp A))). apply FOA_uniform.
eapply uniform_subset with (l2:=trade_prices_of M).
eauto. auto.
assert(Uniform ((sort m_dbp (FOA (sort m_sp M) (sort by_sp A))))). 
assert((sort m_dbp (FOA (sort m_sp M) (sort by_sp A))) [<=]
(FOA (sort m_sp M) (sort by_sp A))).
eauto.
assert(trade_prices_of (sort m_dbp (FOA (sort m_sp M) (sort by_sp A))) [<=]
trade_prices_of (FOA (sort m_sp M) (sort by_sp A))).
eauto.
eapply uniform_subset with 
(l2:=trade_prices_of (FOA (sort m_sp M) (sort by_sp A))) in H3.
eauto. eauto.
apply FOB_uniform. auto. Qed.

       
Theorem FAIR_is_fair (M: list fill_type)(B: list Bid)(A:list Ask)(NDB: NoDup B)
        (NDA: NoDup A)(NZT:(forall m, In m M -> (tq m) > 0))
        (Hanti: (antisymmetric by_sp)/\(antisymmetric by_dbp) )
        (NZA:(forall a0, In a0 A -> (sq a0) > 0)): 
        matching_in B A M-> Is_fair (FAIR M B A) B A.
Proof. {  intros. unfold FAIR. unfold Is_fair.
          assert(HM':matching_in B (sort by_sp A) (sort m_sp M)).
          { 
          eapply match_inv with (A':=(sort by_sp A)) (M':=(sort m_sp M))(B':=B) in H.
          auto. eauto. eauto. eauto. }
          assert(M0match':matching_in B A (FOA (sort m_sp M) (sort by_sp A))).
          {
          eapply FOA_matching in H. all:auto. apply Hanti. }
          set(M0:=(sort m_dbp (FOA (sort m_sp M) (sort by_sp A)))).
          assert(M0match:matching_in B A M0).
          {
          eapply match_inv with (A':=A) (M':=M0)(B':=B) in M0match'. auto.
          subst M0. eauto. auto. auto. }
          split.
          { unfold fair_on_asks. intros. destruct H0. 
            split.
            { assert(HAa:In s (asks_of (FOA (sort m_sp M) (sort by_sp A)))).
              {
              eapply FOA_aux_more_competative_in with(a2:=s').
              eauto. eauto. apply sort_correct. apply by_sp_P. apply by_sp_P.
              auto. eauto. eauto. 
              assert((asks_of (FOB (sort m_dbp (FOA (sort m_sp M) 
              (sort by_sp A))) (sort by_dbp B))) [<=] 
              asks_of (sort m_dbp (FOA (sort m_sp M) (sort by_sp A)))).
              apply FOB_subA.  
              assert(asks_of (sort m_dbp (FOA (sort m_sp M) (sort by_sp A)))
              [<=]asks_of ((FOA (sort m_sp M) (sort by_sp A)))). eauto.
              eauto. }
              assert(asks_of ((FOA (sort m_sp M) (sort by_sp A)))[<=]
              asks_of (sort m_dbp (FOA (sort m_sp M) (sort by_sp A)))). eauto.
              assert(In s (asks_of M0)). 
              eauto. apply FOB_asks_M_subset_asks_FOB.
              { eauto. }
              { (*NZT*) intros. assert(In m (FOA (sort m_sp M) (sort by_sp A))).
                eauto. eapply FOA_NZT with (M:=(sort m_sp M))(A:=(sort by_sp A)).
                eauto. eauto.  eauto. auto.
              }
              { apply M0match. }
              { assert(bids_of M0 [<=] B).
                apply M0match. eauto. }
              { auto. }
       }
       { assert(In s' (asks_of (FOA (sort m_sp M) (sort by_sp A)))).
         {
         assert((asks_of (FOB M0 (sort by_dbp B)))[<=]asks_of M0).
         apply FOB_subA. assert(asks_of M0 [<=]asks_of (FOA (sort m_sp M) (sort by_sp A))).
         subst M0. eauto. eauto.
         }
         symmetry. assert(ttqa M0 s = ttqa (FOB M0 (sort by_dbp B)) s).
         {
         apply FOB_asks_invariant with (M:=M0)(B:=(sort by_dbp B))(a:=s).
         intros. assert(In m (FOA (sort m_sp M) (sort by_sp A))).
         eauto. eapply FOA_NZT with (M:=(sort m_sp M))(A:=(sort by_sp A)).
         eauto. eauto.  eauto. auto. rewrite <- QM_equal_QMb with (B:=sort by_dbp B).
         eapply fill_size_vs_bid_size.
         all:auto. intros. assert(In b (bids_of M0)\/~In b (bids_of M0)).
         eauto. destruct H7. apply M0match. auto.
         apply ttqb_elim in H7. lia.
         assert(bids_of M0 [<=] B). eapply M0match. eauto.
         }
         rewrite <- H6. assert(ttqa M0 s = ttqa (FOA (sort m_sp M) (sort by_sp A)) s).
         {
         apply ttqa_of_perm. subst M0. eauto. }
         rewrite H7. symmetry. apply FOA_asks_fair with (a1:=s)(a2:=s').
         { eauto. }
         { eauto. } 
         { apply sort_correct. apply by_sp_P. apply by_sp_P. }
         { auto. }
         { eapply FOA_aux_more_competative_in with(a2:=s').
           all:auto. eauto. apply sort_correct. apply by_sp_P. apply by_sp_P. }
         auto.
         } }
       { unfold fair_on_bids. intros.
         split. 
         {
           auto. eapply FOB_aux_more_competative_in. all:auto. 
           { intros. assert(In m (FOA (sort m_sp M) (sort by_sp A))).
             eauto. eapply FOA_NZT with (M:=(sort m_sp M))(A:=(sort by_sp A)).
             eauto. eauto.  eauto. auto.
           }
           { eapply sort_correct. apply by_dbp_P.
           apply by_dbp_P. }
           { eauto. }
           { destruct H0. eapply sort_intro in H0.  eauto. }
           { destruct H0. eapply sort_intro in H4.  eauto.
           }
           { auto. } 
         }
         {
          eapply FOB_bids_fair. all:auto. intros.
          { intros. assert(In m (FOA (sort m_sp M) (sort by_sp A))).
            eauto. eapply FOA_NZT with (M:=(sort m_sp M))(A:=(sort by_sp A)).
            eauto. eauto.  eauto. auto.
          }
          eapply sort_correct. apply by_dbp_P.
          apply by_dbp_P. eauto. destruct H0.
          auto. eapply FOB_aux_more_competative_in. all:auto. 
          { intros. assert(In m (FOA (sort m_sp M) (sort by_sp A))).
            eauto. eapply FOA_NZT with (M:=(sort m_sp M))(A:=(sort by_sp A)).
            eauto. eauto.  eauto. auto.
          }
          { eapply sort_correct. apply by_dbp_P.
            apply by_dbp_P.
          }
          { eauto. }
          { apply sort_intro with (lr:=by_dbp) in H0. eauto. }
          { apply sort_intro with (lr:=by_dbp) in H4.  eauto. }
     } } } Qed.

Theorem FAIR_Quantity
 (M: list fill_type)(B: list Bid)(A:list Ask)(NDB: NoDup B)
        (NDA: NoDup A)(NZT:(forall m, In m M -> (tq m) > 0))
                (NZA:(forall a0, In a0 A -> (sq a0) > 0))
        (Hanti: (antisymmetric by_sp)/\(antisymmetric by_dbp) ): 
        matching_in B A M-> QM(M) = QM(FAIR M B A).
Proof. 
          intros. unfold FAIR. unfold Is_fair.
          assert(HM':matching_in B (sort by_sp A) (sort m_sp M)).
          { 
          eapply match_inv with (A':=(sort by_sp A)) 
          (M':=(sort m_sp M))(B':=B) in H.
          auto. eauto. eauto. eauto. }
          assert(M0match':matching_in B A (FOA (sort m_sp M) (sort by_sp A))).
          {
          eapply FOA_matching in H. all:auto. apply Hanti. }
          set(M0:=(sort m_dbp (FOA (sort m_sp M) (sort by_sp A)))).
          assert(M0match:matching_in B A M0).
          {
          eapply match_inv with (A':=A) (M':=M0)(B':=B) in M0match'. auto.
          subst M0. eauto. auto. auto. }
          assert(QM M0 = QM ((FOA (sort m_sp M) (sort by_sp A)))).
          apply QM_perm. subst M0. eauto.
          assert(QM (FOB M0 (sort by_dbp B))=QM(M0)). symmetry.
          apply FOB_size with (A:=A). eauto. eauto.
          { (*NZT*) intros. assert(In m (FOA (sort m_sp M) (sort by_sp A))).
                eauto. eapply FOA_NZT with 
                (M:=(sort m_sp M))(A:=(sort by_sp A)).
                eauto. eauto.  eauto. auto.
          }
          {
                eapply match_inv with (A':=A) 
                (M':=M0)(B':=(sort by_dbp B)) in M0match'. auto.
                subst M0. eauto. auto. auto. 
          }
         assert(QM (FOA (sort m_sp M) 
         (sort by_sp A))=QM(sort m_sp M)). symmetry.
         apply FOA_size with (B:=B). eauto. eauto. eauto. auto.
         assert(QM(M) = QM((sort m_sp M))).
         apply QM_perm. eauto. lia.
       Qed.
       
Theorem FAIR_correct (M: list fill_type)(B: list Bid)(A:list Ask)(NDB: NoDup B)
        (NDA: NoDup A)(NZT:(forall m, In m M -> (tq m) > 0))
         (NZA:(forall a0, In a0 A -> (sq a0) > 0))
        (Hanti: (antisymmetric by_sp)/\(antisymmetric by_dbp) ): 
        matching_in B A M-> 
        (matching_in B A (FAIR M B A))/\(Is_fair (FAIR M B A) B A)/\(QM(M)= QM((FAIR M B A))).
Proof. intros. apply FAIR_is_matching in H as H1. apply FAIR_Quantity in H as H2.
       apply FAIR_is_fair in H as H3. all:auto.
       Qed.


Theorem exists_fair_matching(M: list fill_type)(B: list Bid)(A:list Ask)(NDB: NoDup B)
        (NDA: NoDup A)(NZT:(forall m, In m M -> (tq m) > 0))
         (NZA:(forall a0, In a0 A -> (sq a0) > 0))
        (Hanti: (antisymmetric by_sp)/\(antisymmetric by_dbp) ): matching_in B A M->
                        (exists M':list fill_type, matching_in B A M' 
                        /\ Is_fair M' B A /\ QM(M) = QM(M')).
Proof. intros. exists (FAIR M B A). apply FAIR_correct. all:auto. Qed.

End Fair.




