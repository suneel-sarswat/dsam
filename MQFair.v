
(* ------------   Work to be done : organise the hints properly ------------- *)



(* -------------------------------------------------------------------------------------

      This file contains all the important results about fair matching.
      The main result is existance of a fair matching without compromize of it's size.

       by_sp                 <===>   order by increasing sp and time
       by_dbp                <===>   order by decreasing bp and increasing time (if bp is same)
       Make_FOA M A          <===>   makes M fair on asks A
       Make_FOB M B          <===>   makes M fair on bids B


Some important results:


Theorem exists_fair_matching :
  matching_in B A M-> 
  (exists M':list fill_type, matching_in B A M' /\ Is_fair M' B A /\ |M|= |M'|).

------------------------------------------------------------------------------------------*)







Require Import ssreflect ssrbool. 
Require Export Lists.List.
Require Export GenReflect SetSpecs.
Require Import Lia.
Require Import Wf.
From Equations Require Import Equations.

Require Export DecSort MinMax.
Require Export MQBidAsk.
Require Export DecList.
Require Export MQMatching.

(*Require Export AuctionInvar.*)

Section Fair.
 
Definition fair_on_bids (M: list fill_type)(B: list Bid):=
  (forall b b', In b B /\ In b' B -> b > b' -> In b' (bids_of M) -> (ttqb M b')>0-> (In b (bids_of M)/\(ttqb M b= bq b))).

Definition fair_on_asks (M: list fill_type) (A: list Ask):=
  (forall s s', In s A /\ In s' A -> s < s' -> In s' (asks_of M) ->(ttqa M s')>0 -> (In s (asks_of M)/\(ttqa M s= sq s))).

Definition Is_fair (M: list fill_type) (B: list Bid) (A: list Ask) 
  :=  fair_on_asks M A /\ fair_on_bids M B.



  
(*----------------  Function to make a matching fair on bids -----------------------*)


(*
Program Fixpoint Make_FOB (M:list fill_type) (B: list Bid) {measure (|M| + |B|)}:=
match (M,B) with 
 |(nil,_) => nil
 |(m::M',nil) => nil
 |(m::M',b::B') => match (Nat.eqb (tq m) (bq b)) with
  |true  => (Mk_fill b (ask_of m) (tp m) (tq m))::(Make_FOB M' B')
  |false => match (Nat.leb (tq m) (bq b)) with
    |true  => (Mk_fill b (ask_of m) (tp m) (tq m)):: (Make_FOB M' ((Mk_bid (bp b) (btime b) (bq b - tq m) (idb b))::B'))
    |false => (Mk_fill b (ask_of m) (tp m) (bq b)):: (Make_FOB ((Mk_fill (bid_of m) (ask_of m) (tq m - bq b) (tp m))::M') B') 
end
end
end.

Next Obligation.
simpl. lia. Qed.
Next Obligation.
simpl. lia. Qed.


There are two problems with the above function:1. In program fixpoint, we cant do rewriting. The solution of this problem is to use either Braga method or Equations. 2. The original bq of b has updated, and this is a problem when we wants to use the same b in the next interation. One possible solution is to use B twice in an auxulary program, one for the tracking bq and one to use bids for Mk_fill without changing bq. *)


Equations FOB_aux (M:list fill_type) (B: list Bid)(Bl: list Bid): (list fill_type) by wf (|M| + |B|):=
FOB_aux nil _ _:= nil;
FOB_aux _ nil _:= nil;
FOB_aux _ _ nil:= nil;
FOB_aux (m::M') (b::B') (b'::Bl'):= if (Nat.eqb (tq m) (bq b)) then 

(Mk_fill b' (ask_of m) (tq m) (tp m))::(FOB_aux M' B' Bl') 

else (if (Nat.leb (tq m) (bq b)) then

(Mk_fill b' (ask_of m) (tq m) (tp m)):: (FOB_aux M' ((Mk_bid (bp b) (btime b) (bq b - tq m) (idb b))::B') (b'::Bl'))

else 

(Mk_fill b' (ask_of m) (bq b) (tp m)):: (FOB_aux ((Mk_fill (bid_of m) (ask_of m) (tq m - bq b) (tp m))::M') B' Bl')).

Next Obligation.
lia. Qed.
Next Obligation.
lia. Qed.

Definition FOB (M:list fill_type) (B: list Bid) := FOB_aux M B B.


(*Lemma: The list of Bids of above matching is subset of B2 and the Asks are subset of old M*)

Lemma FOB_bids_subset (M: list fill_type) (B1:list Bid) (B2:list Bid) :
bids_of (FOB_aux M B1 B2) [<=] B2.
Proof. apply FOB_aux_elim. all: auto.
intros. destruct (Nat.eqb (tq f) (bq b)) eqn: Hfb. 
{ simpl. cut (bids_of (FOB_aux l l0 l1) [<=] l1). auto. exact H. }
{ destruct (Nat.leb (tq f) (bq b)) eqn: Hbf. { simpl. eapply subset_elim1. apply H0. }
{  simpl. eapply subset_elim2 with (a:=b0). exact H1. }} Qed.
           
Lemma FOB_asks_subset (M: list fill_type) (B1:list Bid) (B2:list Bid) :
asks_of (FOB_aux M B1 B2) [<=] asks_of M.
Proof. apply FOB_aux_elim. all: auto.
intros. destruct (Nat.eqb (tq f) (bq b)) eqn: Hfb. 
{ simpl. cut (asks_of (FOB_aux l l0 l1) [<=] asks_of l). auto. exact H. }
{ destruct (Nat.leb (tq f) (bq b)) eqn: Hbf. { simpl. eapply subset_elim2. apply H0. }
{  simpl. simpl in H1. eapply subset_elim1. exact H1. }} Qed.

Lemma mfob_ask_sub_M (M: list fill_type)(B: list Bid): asks_of (FOB M B) [<=] asks_of M.
Proof. { unfold FOB. apply FOB_asks_subset. } Qed.
Lemma mfob_subB (M:list fill_type) (B:list Bid): bids_of (FOB M B) [<=] B.
Proof. { unfold FOB. apply FOB_bids_subset. } Qed. 

(*Lemma: Total traded quantity for each bid and ask in above matching does not cross it's original quantity*)

Lemma mfob_ttqb (M: list fill_type)(B: list Bid)(b:Bid): In b (bids_of (FOB M B)) ->
(ttqb (FOB M B)) b <= bq b.
Proof. Admitted.

Lemma mfob_ttq_ask_equal (M: list fill_type)(B: list Bid)(a:Ask): In a (asks_of M) ->
(ttqa M a) = (ttqa (FOB M B) a).
Proof. Admitted.

(*Lemma: All matchable in FOB

Lemma mfob_matchable (M: list fill_type)(B: list Bid): Sorted by_bp B -> Sorted m_dbp M ->
(forall b, In b (bids_of M) -> ttqb M b <= bq b) -> All_matchable (FOB M B).
Proof. Admitted.

Lemma: FOB is matching*)

(*TODO*)

(* -------------- function to make a matching fair on asks --------------------- *)
(*
Program Fixpoint Make_FOA (M:list fill_type) (A: list Ask) {measure (|M| + |A|)}:=
match (M,A) with 
 |(nil,_) => nil
 |(m::M',nil) => nil
 |(m::M',a::A') => match (Nat.eqb (tq m) (sq a)) with
  |true  => (Mk_fill (bid_of m) a (tp m) (tq m))::(Make_FOA M' A')
  |false => match (Nat.leb (tq m) (sq a)) with
    |true  => (Mk_fill (bid_of m) a (tp m) (tq m)):: (Make_FOA M' ((Mk_ask (sp a) (stime a) (sq a - tq m) (ida a))::A'))
    |false => (Mk_fill (bid_of m) a (tp m) (sq a)):: (Make_FOA ((Mk_fill (bid_of m) (ask_of m) (tq m - sq a) (tp m))::M') A') 
end
end
end.

Next Obligation.
simpl. lia. Qed.
Next Obligation.
simpl. lia. Qed.

*)
End Fair.
