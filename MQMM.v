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
Require Export mMM.

Section MM_Process.



Definition MM B A:=  
(MM_aux (sort by_dbp B) (sort by_dsp A) 0 0).



Theorem MM_Is_IR_Matching (B:list Bid)(A:list Ask)
(NZB: forall b, In b B -> (bq b)>0)
(NZA: forall a, In a A -> (sq a)>0)
(NDA:NoDup (idas_of A))
(NDB:NoDup (idbs_of B))
(Hanti: (antisymmetric by_dsp)/\(antisymmetric by_dbp)):
matching_in B A (MM B A)/\Is_IR (MM B A).
Proof. intros. split. eapply MM_Is_Matching.
       all:auto. apply MM_aux_is_Ind_Rat.
       apply sort_correct. apply by_dbp_P.  apply by_dbp_P.
       apply sort_correct. apply by_dsp_P.  apply by_dsp_P.
       Qed.

(*This Theorem says that the total traded volume of MM is greater than 
total traded volume of any matching M which is individual-rational*)

Theorem MM_Maximum (B:list Bid)(A:list Ask)(M:list fill_type)
(NZB: forall b, In b B -> (bq b)>0)
(NZA: forall a, In a A -> (sq a)>0)
(NDA:NoDup (idas_of A))
(NDB:NoDup (idbs_of B))
(NZT: forall m : fill_type, In m M -> tq m > 0)
(Hanti: (antisymmetric by_dsp)/\(antisymmetric by_dbp)):
Sorted by_dbp B ->
Sorted by_dsp A ->
matching_in B A M /\ Is_IR M->
QM((MM B A))>=QM(M).
Proof. intros.
       assert(HA:(sort by_dsp A) = A).
       { 
        apply sort_equal_nodup. apply by_sp_refl. apply Hanti.
        all: auto. 
       }
       assert(HB:(sort by_dbp B)  = B).
       {
        apply sort_equal_nodup. apply by_dbp_refl. apply Hanti.
        all: auto.
       }
        unfold MM.
        rewrite HA.  rewrite HB.
        apply MM_aux_optimal. 
        all: auto. all:apply H1.
Qed.

(*It is easy to see that by aplying FAIR process on UM, we get a fair matching which is maximum since FIAR process does not changes total volume. This proof cab be verified in MQFAIR.v*) 

(*FOllowing process produces a maximum, fair and IR matching.*)

Definition MM_FAIR B A := FAIR (MM B A) B A.

End MM_Process.


Require Extraction.
Extraction  Language Haskell.
Recursive Extraction MM_FAIR.
Extraction  Language OCaml.
Recursive Extraction MM_FAIR.

