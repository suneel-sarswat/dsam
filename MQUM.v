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

Section UM_Process.


(*
Note1: It is natural to believe that the bids and asks comes with 
non-zero quanttity. It is easy to ensure that all the zero quantity bids
or zero quantity asks are removed from the system on arrival.
These assertions below are denoted as NZB and NZA respectively.

Note2: Since no bid or asks is of non-zero quantity a matching can be
assumed to have non-zero transactions. This assertion is represented as
NZT.

Note3: Each bid or ask is assigned a unique time stamp and unique id 
on arrival. So it is easy to see that we do not have two bids or asks with 
same ids in the lists B and A. These assertions are denoted as NDA and NDB.
Similarly, since a bid or ask has a unique time-stamp and they are sorted by
using their time-stamp, they have complete order. This means we can assert that the sorting criteria is anti-symmetric. These assertations are denoted as
Hanti.

Now we state our main theorems.
*)





Definition UM B A:=  
replace_column 
(UM_aux (sort by_dbp B) (sort by_sp A) 0 0) (uniform_price B A).



(*Following Theorem says the The processs UM is Individual Rational 
and Uniform matching. Note that Is_uniform is defined as IR 
and Uniform matching*)
Theorem UM_Is_Uniform (B:list Bid)(A:list Ask)
(NZB: forall b, In b B -> (bq b)>0)
(NZA: forall a, In a A -> (sq a)>0)
(NDA:NoDup (idas_of A))
(NDB:NoDup (idbs_of B))
(Hanti: (antisymmetric by_sp)/\(antisymmetric by_dbp)):
Sorted by_dbp B -> 
Sorted by_sp A -> 
Is_uniform (UM B A) B A.
Proof. intros. 
       assert(HA:(sort by_sp A) = A).
       { 
        apply sort_equal_nodup. apply by_sp_refl. apply Hanti.
        all: auto. 
       }
       assert(HB:(sort by_dbp B)  = B).
       {
        apply sort_equal_nodup. apply by_dbp_refl. apply Hanti.
        all: auto.
       }
        unfold UM.
        rewrite HA.  rewrite HB. 
        assert(Is_uniform (UM_matching B A) B A).
        eapply mUM.UM_Is_Matching.
        eauto. eauto. eauto. eauto.
        unfold UM_matching in H1.
        auto.
Qed.

(*This Theorem says that UM is fair matching.*)

Theorem UM_FAIR (B:list Bid)(A:list Ask)
(NZB: forall b, In b B -> (bq b)>0)
(NZA: forall a, In a A -> (sq a)>0)
(NDA:NoDup (idas_of A))
(NDB:NoDup (idbs_of B))
(Hanti: (antisymmetric by_sp)/\(antisymmetric by_dbp)):
Sorted by_dbp B -> 
Sorted by_sp A -> 
Is_fair (UM B A) B A.
Proof. intros. 
       assert(HA:(sort by_sp A) = A).
       { 
        apply sort_equal_nodup. apply by_sp_refl. apply Hanti.
        all: auto. 
       }
       assert(HB:(sort by_dbp B)  = B).
       {
        apply sort_equal_nodup. apply by_dbp_refl. apply Hanti.
        all: auto.
       }
        unfold UM.
        rewrite HA.  rewrite HB. 
        assert(Is_fair (UM_matching B A) B A).
        apply UM_Fair. all:auto.
Qed.


Theorem UM_Maximum (B:list Bid)(A:list Ask)(M:list fill_type)
(NZB: forall b, In b B -> (bq b)>0)
(NZA: forall a, In a A -> (sq a)>0)
(NDA:NoDup (idas_of A))
(NDB:NoDup (idbs_of B))
(NZT: forall m : fill_type, In m M -> tq m > 0)
(Hanti: (antisymmetric by_sp)/\(antisymmetric by_dbp)):
Sorted by_dbp B -> 
Sorted by_sp A ->
Is_uniform M B A ->
QM((UM B A))>=QM(M).
Proof. intros. 
       assert(HA:(sort by_sp A) = A).
       { 
        apply sort_equal_nodup. apply by_sp_refl. apply Hanti.
        all: auto. 
       }
       assert(HB:(sort by_dbp B)  = B).
       {
        apply sort_equal_nodup. apply by_dbp_refl. apply Hanti.
        all: auto.
       }
        unfold UM.
        rewrite HA.  rewrite HB.
        replace (QM (replace_column (UM_aux B A 0 0) (uniform_price B A)))
        with (QM (UM_aux B A 0 0)).
        apply UM_aux_optimal. 
        all: auto. 
        eapply replace_column_size. 
Qed.



End UM_Process.


Require Extraction.
Extraction  Language Haskell.
Recursive Extraction UM.
Extraction  Language OCaml.
Recursive Extraction UM.

