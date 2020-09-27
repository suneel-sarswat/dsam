
(* -----------------Description----------------------------------------------------------

This file contains useful definitions and basic properties of fundamental concepts 
about auctions such as matching, maximum matching (MM), individual rational matching (IR), 
uniform matching, fair matching etc. This file also contains results on matchings, 
IR matchings, uniform matchings.


    Terms          <==>     Explanations
    -----------------------------------------------------
    All_matchable M        Every bid-ask pair in M are matchable
    matching M             All_matchable M && NoDup B_M && NoDup A_M              
    matching_in B A M      matching M && B_M [<=] B && A_M [<=] A
    Is_MM M B A            M is maximal matching for B and A
    rational m             bid_of m  >= tp m >= ask_of m
    Is_IR M                forall m, In n M -> rational m    
    Uniform M              all bid-ask pairs in M is traded at single price        
    fair_on_bids B M       M is fair on all bids (i.e. B)
    fair_on_asks A M       M is fair on all asks (i.e. A) 
    Is_fair M B A          M is fair on B and A

Most of the results in this file contains the introduction and elimination rules 
for all the above defined notions.

-----------------------------------------------------------------------------*)

Require Import ssreflect ssrbool.
Require Export Lists.List.
Require Export GenReflect SetSpecs.
Require Export DecList.
Require Export DecSort.
Require Export mBidAsk.
Require Export Quantity.
Section Matching.

  
(*----------------- Notion of matching and  Maximal Matching (MM) ------------------------*)

(* Definition matchable (b: Bid)(a: Ask):=  (sp (a)) <= (bp (b)). *)

  Definition All_matchable (M: list fill_type):= forall m, In m M -> (ask_of m) <= (bid_of m).


Definition all_matchable (M:list fill_type) := forallb (fun m => 
 Nat.leb (ask_of m) (bid_of m)) M.

Lemma all_matchableP (M:list fill_type): reflect (All_matchable M) (all_matchable M).
Proof. {  apply reflect_intro.  unfold Prop_bool_eq. split.
          { induction M. intros. simpl. auto. intros. simpl. apply /andP. split.
            apply /leP. unfold All_matchable in H. apply H. auto.
            assert (H1: All_matchable M).
            revert H. unfold All_matchable. simpl. auto.  apply IHM in H1. eauto. }
          { induction M. intros. unfold All_matchable. intros. destruct H0.
            simpl. intros. move /andP in H. destruct H. unfold All_matchable. intros. 
            destruct H1. move /leP in H. subst a. exact. eapply IHM in H0. 
            unfold All_matchable in H0. eapply H0 in H1. exact. } } Qed.

Definition matching (M: list fill_type):=
  (All_matchable M) /\ 
  (forall b, In b (bids_of M) -> (ttqb M b) <= (bq b)) /\ 
  (forall a, In a (asks_of M) -> (ttqa M a) <= (sq a)).


  
Definition matching_in (B:list Bid) (A:list Ask) (M:list fill_type):=
(matching M) /\ ((bids_of M) [<=] B) /\ ((asks_of M) [<=] A).

Definition Is_MM (M : list fill_type)(B: list Bid)(A: list Ask) :=
  matching_in B A M /\ 
  (forall M': list fill_type, matching_in B A M' -> QM(M') <= QM(M)).

Lemma All_matchable_elim (m: fill_type)(M: list fill_type):
  All_matchable (m::M) -> (ask_of m) <= (bid_of m).
Proof.  intros H.  unfold All_matchable in H. simpl in H. auto.  Qed.   
 

Lemma All_matchable_elim1 (m: fill_type)(M: list fill_type):
  All_matchable (m::M) -> All_matchable M.
Proof.  unfold All_matchable. intros.  simpl in H. auto. Qed.

Lemma All_matchable_elim2  (m: fill_type)(M: list fill_type):
  All_matchable M -> All_matchable (delete m M).
Proof. unfold All_matchable. intros. apply H. eapply delete_elim1. eauto. Qed.  

Definition empty_fill: list fill_type:= nil.

Lemma All_matchable_nil: All_matchable nil.
Proof. unfold All_matchable. intros. inversion H. Qed.  

Lemma All_matchable_intro (m: fill_type)(M: list fill_type):
  (ask_of m) <= (bid_of m) -> All_matchable M -> All_matchable (m::M).
Proof. { intros H1 H2. unfold All_matchable. simpl. intros m0 H3. destruct H3.
         subst m0. exact. eauto. } Qed. 


Hint Immediate All_matchable_intro All_matchable_nil: core.
Hint Resolve All_matchable_elim All_matchable_elim1 All_matchable_elim2 : core.

Lemma nill_is_matching (B: list Bid)(A: list Ask) : matching_in B A nil.
Proof. { unfold matching_in. split. unfold matching.
         split. apply All_matchable_nil.
         split. simpl. intros. destruct H. simpl. intros. destruct H.
         split. simpl. auto. simpl. auto. } Qed.
Hint Resolve nill_is_matching: core.

(*-------------introduction and elimination for matching ------------------------*)

(*-------    Definition matching (M: list fill_type):=
             (All_matchable M) /\ (NoDup (bids_of M)) /\ (NoDup (asks_of M)).    *)

Lemma matching_elim0 (m: fill_type) (M: list fill_type): matching M -> In m M ->
                                                         (ask_of m) <= (bid_of m).
Proof. intros. unfold matching in H.  destruct H. unfold All_matchable in H.
apply H in H0. exact. Qed.

Lemma matching_elim1 (M: list fill_type): matching M -> (forall b, In b (bids_of M) -> (ttqb M b) <= (bq b)).
Proof.  intro H. unfold matching in H. destruct H. destruct H0. exact. Qed.

Lemma matching_elim2 (M: list fill_type): matching M -> (forall a, In a (asks_of M) -> (ttqa M a) <= (sq a)).
Proof. intro H. unfold matching in H. destruct H. destruct H0. exact. Qed.

(*
Lemma matching_elim3 (M: list fill_type): matching M -> NoDup M.
Proof. { intro H. destruct H. destruct H0.
         induction M as [|m].
         { auto. }
         { constructor. intro H2. assert (H4: In (bid_of m) (bids_of M)). eauto.
           simpl in H0. assert (H5: ~In (bid_of m) (bids_of M)). eauto. contradiction.
           apply IHM. all: eauto. } } Qed.



Lemma matching_elim4 (m: fill_type) (M: list fill_type): matching (m::M) ->
                                                         ~ In (ask_of m) (asks_of M).
Proof. { intros. unfold matching in H. destruct H. destruct H0. simpl in H1.
         eapply nodup_elim2 in H1. exact. } Qed.

Lemma matching_elim5 (m: fill_type) (M: list fill_type): matching (m::M) ->
                                                         ~ In (bid_of m) (bids_of M).
Proof. { intros. unfold matching in H. destruct H. destruct H0. simpl in H0.
         eapply nodup_elim2 in H0. exact. } Qed.
*)

Lemma matching_elim6 (m: fill_type) (M: list fill_type): matching (m::M) -> matching M.
Proof. { intros. unfold matching in H. destruct H. destruct H0. unfold matching.
         split. eapply All_matchable_elim1. eauto. split. 
         { intros. simpl in H0. specialize (H0 b) as Hb. destruct Hb.
         right. exact. destruct (b_eqb b (bid_of m)). lia. lia.
         destruct (b_eqb b (bid_of m)). lia. lia. }
         { intros. simpl in H1. specialize (H1 a) as Ha. destruct Ha.
         right. exact. destruct (a_eqb a (ask_of m)). lia. lia.
         destruct (a_eqb a (ask_of m)). lia. lia. } } Qed.

(*
Lemma matching_elim14 (m1 m2: fill_type) (M: list fill_type): matching M -> In m1 M -> In m2 M ->
                                                              m1 <> m2 -> bid_of m1 <> bid_of m2.
Proof. { induction M.
         { intros. destruct H0. }
         { intros.  destruct H. destruct H3. destruct H1;destruct H0.
           { subst m1. subst m2. destruct H2. exact. }
           { subst a. simpl in H4.
             assert (H5: In (bid_of m1) (bids_of M)). eauto. 
             assert (H6: ~ In (bid_of m2) (bids_of M)). eauto.
             intro h7. rewrite h7 in H5. contradiction. } 
           { subst a. simpl in H4.
             assert (H5: In (bid_of m2) (bids_of M)). eauto. 
             assert (H6: ~ In (bid_of m1) (bids_of M)). eauto.
             intro h7. rewrite h7 in H6. contradiction. }
           { apply IHM. unfold matching;eauto. all: exact. } } } Qed.

Lemma matching_elim15 (m1 m2: fill_type) (M: list fill_type): matching M -> In m1 M -> In m2 M ->
                                                              m1 <> m2 -> ask_of m1 <> ask_of m2.
Proof.  { induction M.
          { intros. destruct H0. } 
          { intros.  destruct H. destruct H3. destruct H1;destruct H0. 
            { subst m1. subst m2. destruct H2. exact. }
            { subst a. simpl in H4.
              assert (H5: In (ask_of m1) (asks_of M)). eauto. 
              assert (H6: ~ In (ask_of m2) (asks_of M)). eauto.
              intro h7. rewrite h7 in H5. contradiction. } 
            { subst a. simpl in H4.
              assert (H5: In (ask_of m2) (asks_of M)). eauto. 
              assert (H6: ~ In (ask_of m1) (asks_of M)). eauto.
              intro h7. rewrite h7 in H6. contradiction. }
            { apply IHM. unfold matching;eauto. all: exact. } } } Qed.



Lemma matching_elim7 (m: fill_type) (M: list fill_type): In m M -> matching M ->
                                                         ~ In (ask_of m) (asks_of (delete m M)).
Proof.  { intros H1 H2. unfold matching in H2.
          destruct H2. destruct H0.
          intro H3.
          assert (H4: exists m', (In m' (delete m M))/\ (ask_of m = ask_of m')).
          eauto. destruct H4 as [m' H4]. destruct H4 as [H4 H5].
          assert (H6: In m' M). eapply included_elim2. eapply included_elim4.
          apply included_intro2. exact H1. apply included_intro2. exact H4.
          apply included_refl. assert (H7: m'<>m).
          cut (NoDup M).
          { intro. eapply delete_elim2. exact H7. exact H4. }
          apply matching_elim3. unfold matching. auto.
          eapply matching_elim15 in H7. symmetry in H5.
          contradiction. instantiate (1:=M).
          unfold matching. auto. exact. exact. } Qed.
 
  

Lemma matching_elim8 (m: fill_type) (M: list fill_type): In m M -> matching M ->
                                                         ~ In (bid_of m) (bids_of (delete m M)).
Proof.  { intros H1 H2. unfold matching in H2. destruct H2. destruct H0.
          intro H3.
          assert (H4: exists m', (In m' (delete m M))/\ (bid_of m = bid_of m')). eauto.
          destruct H4 as [m' H4]. destruct H4 as [H4 H5].
          assert (H6: In m' M). 
          eapply included_elim2. eapply included_elim4.
          apply included_intro2. exact H1. apply included_intro2. exact H4.
          apply included_refl.
          assert (H7: m'<>m).
          cut (NoDup M). intro. eapply del_all_elim2. 
          apply del_all_intro. exact H6. eapply delete_elim2.
          exact H7. exact H4.
          apply matching_elim3.
          unfold matching. auto. eapply matching_elim14 in H7.
          symmetry in H5. contradiction. instantiate (1:=M).
          unfold matching. auto. exact. exact. } Qed.

*)

Lemma matching_elim9 (m: fill_type) (M: list fill_type): matching M ->  matching (delete m M).
Proof. { intros H. unfold matching in H. destruct H. destruct H0.
         unfold matching. split. 
         { eauto. }
         split.
         {  intros. admit. }
         { intros. admit. } } Admitted.
(*
Lemma matching_elim10 (m: fill_type) (M: list fill_type): matching M -> In m M ->
                                                          ~ In (bid_of m) (bids_of (delete m M)).
Proof. intros. eapply  matching_elim8. exact. exact. Qed.

Lemma matching_elim11 (m: fill_type) (M: list fill_type): matching M -> In m M ->
                                                          ~ In (ask_of m) (asks_of (delete m M)).
Proof. intros. eapply  matching_elim7. all: exact. Qed.

Lemma matching_elim12 (m: fill_type) (M: list fill_type): matching (m::M) ->
                                                          ~ In (bid_of m) (bids_of M).
Proof. { intros. intro. destruct H. destruct H1.  simpl in H1.
         eapply nodup_elim2 in H1. contradiction. } Qed.

Lemma matching_elim13 (m: fill_type) (M: list fill_type): matching (m::M) ->
                                                          ~ In (ask_of m) (asks_of M).
Proof. { intros. intro. destruct H. destruct H1.  simpl in H2. eapply nodup_elim2 in H2.
         contradiction. } Qed.


*)

Hint Resolve matching_elim0 matching_elim1 matching_elim2 (*matching_elim3*): core.
Hint Resolve (*matching_elim4 matching_elim5 matching_elim7 *) matching_elim6: core.
Hint Resolve matching_elim9 (*matching_elim8 matching_elim10 matching_elim11*): core.
(*
Hint Resolve matching_elim12 matching_elim13: core.
Hint Resolve matching_elim14 matching_elim15: core.
*)

(*-----------------introduction and elimination for matching_in -----------------*)          
(*                                               
Lemma matching_in_intro (m: fill_type) (M: list fill_type)(B: list Bid)(A: list Ask):
  (ask_of m) <= (bid_of m) -> matching_in B A M -> ~ In (bid_of m) (bids_of M) ->
  ~ In (ask_of m) (asks_of M) -> In (bid_of m) B -> In (ask_of m) A -> matching_in B A (m::M).

Proof.  { intros H1 H2 H3 H4 H5 H6. unfold matching_in. split.
          unfold matching in H2. destruct H2. destruct H. destruct H2.
          destruct H0. unfold matching.
          split. eauto. split. simpl. eapply nodup_intro in H3. exact. exact.
          eapply nodup_intro in H4. exact. exact. destruct H2. destruct H0. split.
          simpl. unfold "[<=]". intros. destruct H7. subst a. exact. eauto.
          simpl. unfold "[<=]". intros. destruct H7. subst a. exact. eauto. } Qed.
*)
  Lemma matching_in_elim0 (M: list fill_type)(B: list Bid)(A: list Ask): matching_in B A M ->
                                                                         matching M.
  Proof. intros. unfold matching_in in H. destruct H. exact. Qed.
  
  
Lemma matching_in_elim (m: fill_type) (M: list fill_type)(B: list Bid)(A: list Ask):
  matching_in B A (m::M) -> matching_in B A M.
Proof. { intros. unfold matching_in in H. destruct H. destruct H0. 
         unfold matching_in. split. eauto. split. eauto. eauto. } Qed.

Lemma matching_in_elim1 (m: fill_type) (M: list fill_type) (B: list Bid)(A: list Ask):
  matching_in B A (m::M) ->  (ask_of m) <= (bid_of m).
Proof. { unfold matching_in. intros H. destruct H as [H1 H].
         destruct H1 as [H1 H2]. eauto. } Qed.
 
(*
Lemma matching_in_elim2 (m: fill_type) (M: list fill_type) (B: list Bid)(A: list Ask):
  matching_in B A (m::M) ->   ~ In (bid_of m) (bids_of M).
Proof. { unfold matching_in;unfold matching. intros H.
         destruct H as [H1 H]. destruct H as [H2 H]. destruct H1 as [H1 H3].
         destruct H3 as [H3 H4]. eauto. } Qed.


Lemma matching_in_elim3 (m: fill_type) (M: list fill_type) (B: list Bid)(A: list Ask):
  matching_in B A (m::M) ->   ~ In (ask_of m) (asks_of M).
Proof. { unfold matching_in;unfold matching. intros H.
         destruct H as [H1 H]. destruct H as [H2 H]. destruct H1 as [H1 H3].
         destruct H3 as [H3 H4]. eauto. } Qed.

*)

Lemma matching_in_elim4 (m: fill_type) (M: list fill_type) (B: list Bid)(A: list Ask):
  matching_in B A (m::M) ->   In (bid_of m) B.
Proof. { unfold matching_in;unfold matching. intros H.
         destruct H as [H1 H]. destruct H as [H2 H]. destruct H1 as [H1 H3].
         destruct H3 as [H3 H4]. eauto. } Qed.

Lemma matching_in_elim4a (m: fill_type) (M: list fill_type) (B: list Bid)(A: list Ask):
  matching_in B A M -> In m M ->  In (bid_of m) B.
Proof. intros. destruct H. destruct H1. eauto. Qed.


Lemma matching_in_elim5 (m: fill_type) (M: list fill_type) (B: list Bid)(A: list Ask):
  matching_in B A (m::M) ->   In (ask_of m) A.
Proof. { unfold matching_in;unfold matching. intros H.
         destruct H as [H1 H]. destruct H as [H2 H]. destruct H1 as [H1 H3].
         destruct H3 as [H3 H4]. eauto. } Qed.

Lemma matching_in_elim5a (m: fill_type) (M: list fill_type) (B: list Bid)(A: list Ask):
  matching_in B A M ->  In m M -> In (ask_of m) A.
Proof. intros. unfold matching_in in H. destruct H. destruct H1. eauto. Qed.


Lemma matching_in_elim6 (a: Ask)(B: list Bid)(A: list Ask)(M: list fill_type):
  matching_in B A M -> matching_in B (a::A) M.
Proof. { unfold matching_in. intros. destruct H. destruct H0. split. exact.
         split. exact. eauto. } Qed.

Lemma matching_in_elim7 (b: Bid)(B: list Bid)(A: list Ask)(M: list fill_type):
  matching_in B A M -> matching_in (b::B) A M.
Proof. { unfold matching_in. intros. destruct H. destruct H0. split. exact.
         split. eauto. exact. } Qed.

Lemma matching_in_elim7a (m: fill_type)(B: list Bid)(A: list Ask)(M: list fill_type):
matching_in B A M -> matching_in B A (delete m M).
  
Proof. { unfold matching_in. intros. destruct H. destruct H0. split. eauto. split. eauto. eauto. } Qed.

 Lemma matching_in_elim8 (B: list Bid)(A: list Ask)(b: Bid)(a: Ask)(M: list fill_type):
   matching_in (b::B) (a::A) M -> ~ In b (bids_of M) -> ~ In a (asks_of M) -> matching_in B A M.
 Proof. { unfold matching_in. intros. destruct H. destruct H2. destruct H.
          destruct H4. unfold matching. split.
          { split. { exact. } { eauto. } }
          split. 
          
          { admit. }
          { admit. } } Admitted.
  

Hint Resolve matching_in_elim4a matching_in_elim5a: core. 
(*Hint Immediate matching_in_intro: auction.*)
Hint Resolve matching_in_elim0 matching_in_elim matching_in_elim1 (*matching_in_elim2
     matching_in_elim3 *) matching_in_elim4 matching_in_elim5 : auction.

Hint Resolve matching_in_elim6 matching_in_elim7 matching_in_elim7a  matching_in_elim8: core.

(*----------------- Individual rational and  Fair matching--------------------------*)

Definition rational (m: fill_type):=
  ((bid_of m) >= tp m) /\ (tp m >= (ask_of m)).
Definition Is_IR (M: list fill_type):= forall m, In m M -> rational m.

Lemma Is_IR_elim (m: fill_type)(M: list fill_type): Is_IR (m::M) -> rational m.
Proof. { unfold Is_IR. intros H.  specialize H with m. simpl in H.
         destruct H. left. exact. unfold rational. eauto. } Qed.

Lemma Is_IR_elim1 (m: fill_type)(M: list fill_type): Is_IR (m::M)-> Is_IR M.
Proof. unfold Is_IR. simpl. intros. eauto. Qed.

Lemma Is_IR_elim2 (m: fill_type)(M: list fill_type): Is_IR M -> Is_IR (delete m M).
Proof. unfold Is_IR. intros. eauto. Qed.

Lemma Is_IR_intro (m: fill_type)(M: list fill_type): rational m -> Is_IR M -> Is_IR (m::M).
Proof.  unfold Is_IR. intros. destruct H1. subst m0. exact. auto. Qed.  

Hint Immediate Is_IR_intro: auction.
Hint Resolve Is_IR_elim Is_IR_elim1: auction.


(*------------------Uniform matching------------------------------*)


Definition Uniform (M : list fill_type) := uniform (trade_prices_of M).

Lemma tps_of_delete (M: list fill_type) (m: fill_type) (x:nat):
  In x (trade_prices_of (delete m M)) -> In x (trade_prices_of M).
  Proof. { intro H. 
         assert (H1: exists m', In m' (delete m M) /\ (x=(tp m'))).
         eauto. destruct H1 as [m' H1]. destruct H1 as [H1 H2].
         cut (In m' M). subst x. eauto. 
         eapply delete_elim1. exact H1. } Qed.
  
Lemma Uniform_intro (M:list fill_type) (m:fill_type) : Uniform M -> Uniform (delete m M).
Proof. { unfold Uniform. intro H.
         case M as [|m' M'] eqn: HM.
         { simpl. constructor. }
         { simpl in H. assert ((forall x, In x (tp m' :: trade_prices_of M')-> x= (tp m'))).
           eapply uniform_elim1. exact.
           simpl. destruct (m_eqb m m') eqn: Hm.
           { apply uniform_elim2 in H.  exact. }
           { simpl. cut (forall x, In x (trade_prices_of (delete m M')) -> x=(tp m')).
             eapply uniform_intro. intros x H1.
             assert (H1b: In x (trade_prices_of M')).
             { eapply tps_of_delete. exact H1. }
             apply H0. auto. }}} Qed.
          

Lemma Uniform_intro1 (M:list fill_type) (m:fill_type) : Uniform (m::M) -> Uniform M.
Proof. unfold Uniform.  simpl.  eapply uniform_elim2. Qed.

Lemma Uniform_elim (M:list fill_type) (m1 m2:fill_type) :
  Uniform M -> In m1 M -> In m2 M -> tp m1 = tp m2.
Proof. { unfold Uniform. intros H1 H2 H3. 
         cut (In (tp m2) (trade_prices_of M)).
         cut (In (tp m1) (trade_prices_of M)).
         eapply uniform_elim4. exact. all:auto. } Qed.

Lemma Uniform_intro2 (M:list fill_type) (m m':fill_type) : Uniform M -> 
In m M -> tp m = tp m' -> Uniform (m'::M).
Proof. { unfold Uniform. intros H1 H2 H3.
         assert (H0:In (tp m) (trade_prices_of M)).
         auto. simpl. eapply uniform_intro. intros x H4.
         rewrite <- H3. eapply uniform_elim4. exact H1. all:auto. } Qed.

Hint Resolve Uniform_intro  Uniform_intro1 Uniform_elim : core.
Hint Immediate Uniform_intro2 : core.

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

Hint Resolve buyers_above_elim buyers_above_intro: auction.
Hint Resolve sellers_above_elim sellers_above_intro: auction.

Hint Resolve buyers_below_elim buyers_below_intro: auction.
Hint Resolve sellers_below_elim sellers_below_intro: auction.


Theorem buyers_above_ge_sellers (p:nat)(M: list fill_type) (B: list Bid) (A: list Ask):
  matching_in B A M -> | buyers_above p (bids_of M)| >= | sellers_above p (asks_of M)|.
 Proof. { intros H. destruct H as [H H0]. destruct H0 as [H0 H1]. 
          destruct H as [H H2]. destruct H2 as [H2 H3].
          induction M. 
          { simpl. auto. }
          { simpl.  
            destruct (Nat.leb p (bid_of a)) eqn: Hpb.
            { destruct (Nat.leb p (ask_of a)) eqn: Hpa.
              { simpl. cut ((| buyers_above p (bids_of M) |) >= (| sellers_above p (asks_of M) |)). 
            lia. apply IHM. all:eauto. admit. admit. }
              { simpl. cut ((| buyers_above p (bids_of M) |) >= (| sellers_above p (asks_of M) |)). 
            lia. apply IHM. all:eauto. admit. admit. } }
            { destruct (Nat.leb p (ask_of a)) eqn: Hpa.
              { move /leP in Hpb. move /leP in Hpa. 
                unfold All_matchable in H. assert (H4: (ask_of a <= bid_of a)). 
                apply H. auto. lia. }
              { apply IHM. all: eauto. admit. admit. }}}} Admitted.

Theorem sellers_below_ge_buyers (p:nat)(M: list fill_type) (B: list Bid) (A: list Ask):
  matching_in B A M -> | buyers_below p (bids_of M)| <= | sellers_below p (asks_of M)|.
Proof. { intros H. destruct H as [H H0]. destruct H0 as [H0 H1]. 
          destruct H as [H H2]. destruct H2 as [H2 H3].
          induction M. 
          { simpl. auto. }
          { simpl.  
            destruct (Nat.leb (bid_of a) p) eqn: Hpb.
            { destruct (Nat.leb (ask_of a) p) eqn: Hpa.
              { simpl. cut ((| buyers_below p (bids_of M) |) <= (| sellers_below p (asks_of M) |)). 
            lia. apply IHM. all:eauto. admit. admit. }
              { move /leP in Hpb. move /leP in Hpa. 
                unfold All_matchable in H. 
                assert (H4: (ask_of a <= bid_of a)). 
                apply H. auto. lia. } }
            { destruct (Nat.leb (ask_of a) p) eqn: Hpa.
              { simpl. cut ((| buyers_below p (bids_of M) |) <= (| sellers_below p (asks_of M) |)). 
            lia. apply IHM. all:eauto. admit. admit.
              }
              { apply IHM. all: eauto. admit. admit. }}}} Admitted.


Lemma matchable_buy_above_sell_below (b:Bid) (a: Ask) (B: list Bid) (A: list Ask) (p:nat): In b (buyers_above p B) -> In a (sellers_below p A)
-> a<=b.
Proof. intros. apply  buyers_above_elim in H. apply sellers_below_elim in H0. lia. Qed. 

Lemma buy_below_above_total (M: list fill_type) (B:list Bid) (A:list Ask) (p:nat):
(matching_in B A M) -> (|(buyers_above p (bids_of M))|) + (|(buyers_below p (bids_of M))|) >= |M|.
Proof. { intros H. destruct H as [H H0]. destruct H0 as [H0 H1]. 
          destruct H as [H H2]. destruct H2 as [H2 H3].
          induction M. { simpl. auto. }
           { simpl.  
            destruct (Nat.leb p (bid_of a)) eqn: Hpb.
            { destruct (Nat.leb (bid_of a) p) eqn: Hpa.
            { simpl. cut ((| buyers_above p (bids_of M) |) + (| buyers_below p (bids_of M) |) >= |M|). 
            lia. apply IHM. all:eauto. admit. admit. }
            { simpl. cut ((| buyers_above p (bids_of M) |) + (| buyers_below p (bids_of M) |) >= |M|). 
            lia. apply IHM. all:eauto. admit. admit. } }
            { destruct (Nat.leb (bid_of a) p) eqn: Hpa.
            { simpl. cut ((| buyers_above p (bids_of M) |) + (| buyers_below p (bids_of M) |) >= |M|). lia. apply IHM. all:eauto. admit. admit. }
            { move /leP in Hpb. move /leP in Hpa. lia. } }}} Admitted.
            
Lemma sell_below_above_total (M: list fill_type) (B:list Bid) (A:list Ask) (p:nat):
(matching_in B A M) -> (|(sellers_above p (asks_of M))|) + (|(sellers_below p (asks_of M))|) >= |M|.
Proof. { intros H. destruct H as [H H0]. destruct H0 as [H0 H1]. 
          destruct H as [H H2]. destruct H2 as [H2 H3].
          induction M. { simpl. auto. }
           { simpl.  
            destruct (Nat.leb p (ask_of a)) eqn: Hpb.
            { destruct (Nat.leb (ask_of a) p) eqn: Hpa.
            { simpl. cut ((|(sellers_above p (asks_of M))|) + (|(sellers_below p (asks_of M))|) >= |M|). 
            lia. apply IHM. all:eauto. admit. admit. }
            { simpl. cut ((|(sellers_above p (asks_of M))|) + (|(sellers_below p (asks_of M))|) >= |M|). 
            lia. apply IHM. all:eauto. admit. admit. } }
            { destruct (Nat.leb (ask_of a) p) eqn: Hpa.
            { simpl. cut ((|(sellers_above p (asks_of M))|) + (|(sellers_below p (asks_of M))|) >= |M|). lia. apply IHM. all:eauto. admit. admit. }
            { move /leP in Hpb. move /leP in Hpa. lia. } }}} Admitted.


Lemma maching_buyer_right_plus_seller_left 
(M: list fill_type) (B:list Bid) (A:list Ask) (p:nat):
(matching_in B A M) -> (|(buyers_above p (bids_of M))|) + (|(sellers_below p (asks_of M))|) >= |M|.
Proof.  intros H. apply sellers_below_ge_buyers with (p:=p) in H  as H1.
                  eapply buyers_above_ge_sellers with (p:=p) in H as H2.
                  eapply buy_below_above_total with (p:=p) in H as H3.
                  eapply sell_below_above_total with (p:=p) in H as H4.
                  lia. Qed.

Lemma matching_size_bids (M:list fill_type)(A:list Ask)(B:list Bid)(NDB:NoDup B):
matching_in B A M -> QM(M) <= QB(B). 
Proof. intros. destruct H. destruct H0. destruct H. destruct H2.
rewrite <- QM_equal_QMb with (B:=B). apply fill_size_vs_bid_size.
auto. apply ttqb_BM_t_B. all:auto. Qed.



End Matching.


Hint Unfold All_matchable : core.
Hint Immediate All_matchable_intro All_matchable_nil: core.
Hint Resolve All_matchable_elim All_matchable_elim1 All_matchable_elim2 : core.

Hint Resolve matching_elim0 matching_elim1 matching_elim2 (*matching_elim3*): core.
Hint Resolve (*matching_elim4 matching_elim5 matching_elim7 *) matching_elim6: core.
Hint Resolve (*matching_elim8*) matching_elim9: core.
(*Hint Resolve matching_elim10 matching_elim11: core.
Hint Resolve matching_elim12 matching_elim13: core.
Hint Resolve matching_elim14 matching_elim15: core.
*)
Hint Resolve nill_is_matching: core.
(*Hint Immediate matching_in_intro: core.*)
Hint Resolve matching_in_elim0 matching_in_elim matching_in_elim1: core.
Hint Resolve (*matching_in_elim2 matching_in_elim3 *) matching_in_elim4: core.
Hint Resolve matching_in_elim4a matching_in_elim5a: core. 
Hint Resolve matching_in_elim5 matching_in_elim6 matching_in_elim7 matching_in_elim7a matching_in_elim8: core.
Hint Immediate Is_IR_intro: core.
Hint Resolve Is_IR_elim Is_IR_elim1: core.

Hint Resolve Uniform_intro Uniform_elim Uniform_intro1 : core.
Hint Immediate Uniform_intro2 : core. 

