
(* -----------------Description------------------------------------------

This file is about Individual Rational (IR) matchings. It contains a
function to convert any matching to an IR matching, it also contains
existensial results of IR matching. The file contains a function produce_IR, which converts any matching M into a Individual Rational matching.

Some important results:

Theorem exists_IR_matching : matching_in B A M -> 
(exists M': list fill_type, bids_of M = bids_of M' /\ asks_of M = asks_of M'
/\ matching_in B A M' /\ Is_IR M').

*)

Require Import ssreflect ssrbool.
Require Export Lists.List.
Require Export GenReflect SetSpecs.

Require Export MQBidAsk.
Require Export DecList.
Require Export MQMatching.


Section IndRat.

(* ----------------- There exists an Individual Rational Matching------------------------ *)
  
Fixpoint produce_IR (M:list fill_type):(list fill_type):=
  match M with
  |nil => nil
  |m::M' => (Mk_fill (bid_of m) (ask_of m) (sp (ask_of m)))::(produce_IR M')
  end.
(*Change it to mid-price of the bid-ask price rather than ask price *)


Lemma fst_same_IR (M: list fill_type) :
  forall m', In m' (produce_IR M) -> exists m, In m M /\ (bid_of m = bid_of m') /\ (ask_of m = ask_of m').
Proof. { intros m' H. induction M. simpl in H. contradiction.
         simpl in H.  destruct H. exists a. split. auto.
         subst m'. simpl;auto. auto.
         assert (H1:  exists m : fill_type, In m M /\ (bid_of m = bid_of m') /\
                                       (ask_of m = ask_of m')); auto.
         destruct H1 as [m H1]. destruct H1.  exists m. split; eauto. } Qed.


  
Lemma same_bids (M:list fill_type):
  (bids_of M) = (bids_of (produce_IR M)).
Proof. { induction M. simpl. auto. simpl. rewrite IHM. auto. } Qed.

Lemma same_asks (M:list fill_type):
  (asks_of M) = (asks_of (produce_IR M)).
Proof. { induction  M. simpl. auto. simpl. rewrite IHM. auto. } Qed.

Lemma produce_IR_is_matching (M: list fill_type) (B: list Bid) (A: list Ask):
  matching_in B A M-> (matching_in B A (produce_IR M)).
Proof. { intro H0. unfold matching_in. unfold matching. 
          unfold All_matchable.   split. split.
           { intros m' H1. 
           assert (H2: exists m, (In m M) /\ ((bid_of m = bid_of m') /\      
           (ask_of m = ask_of m'))). apply fst_same_IR. auto.
            destruct H2 as [m H2]. destruct H2 as [H2 H3]. 
            destruct H3 as [H3 H4]. rewrite <- H3. rewrite <- H4. 
            apply H0. auto. }
        { replace (bids_of (produce_IR M)) with (bids_of M).
          replace (asks_of (produce_IR M)) with (asks_of M). apply H0.
          apply same_asks. apply same_bids. }
           { replace (bids_of (produce_IR M)) with (bids_of M).
          replace (asks_of (produce_IR M)) with (asks_of M). apply H0.
          apply same_asks. apply same_bids. }
          } Qed.  

Lemma produce_IR_trade_ask_same (M:list fill_type):
  forall m: fill_type, In m (produce_IR M) -> sp (ask_of m)=(tp m).
Proof. {  intros m H0. induction M. simpl in H0. contradiction.
           simpl in H0. destruct H0. subst m. simpl. unfold ask_of. simpl. auto. auto. } Qed.
                    
Lemma produce_IR_is_IR (M: list fill_type) (B: list Bid) (A: list Ask):
 matching_in B A M-> Is_IR (produce_IR M).
 
Proof. { intro H0. unfold Is_IR. intro m'. intro H.
         unfold rational. replace (tp m') with (sp (ask_of m')). 2:{
         apply produce_IR_trade_ask_same with (M:=M). auto. } split. 2:{ auto. }
         assert (H1: exists m, In m M /\ (bid_of m = bid_of m') /\ (ask_of m = ask_of m')).
         apply fst_same_IR;auto.
         destruct H1 as [m H1]. destruct H1 as [H1 H2].
         destruct H2 as [H2 H3]. rewrite <- H2. rewrite <-H3. destruct H0 as [H0 H4].
         unfold matching in H0. destruct H0 as [H0 H5].
         unfold All_matchable in H0. apply H0. 
         exact. } Qed.

Theorem exists_IR_matching (M: list fill_type) (B: list Bid) (A:list Ask):
  matching_in B A M -> (exists M': list fill_type, bids_of M = bids_of M' /\ asks_of M = asks_of M'
                                               /\ matching_in B A M' /\ Is_IR M').
Proof. { intros  H.   exists (produce_IR M). split. apply same_bids. split. apply same_asks.
         split. apply produce_IR_is_matching. auto. eapply produce_IR_is_IR. eauto. } Qed.




End IndRat.
