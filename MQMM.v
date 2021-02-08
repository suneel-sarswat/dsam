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


Hypothesis unique_timestampbid:forall b1 b2, (btime b1 = btime b2) -> b1 = b2.
Hypothesis unique_timestampask:forall s1 s2, (stime s1 = stime s2) -> s1 = s2.

Definition MM B A:=  
(MM_aux (sort by_dbp B) (sort by_dsp A) 0 0).



Lemma MM_aux_NZT (B:list Bid)(A:list Ask)(b:Bid)(a:Ask)(tb ta:nat)
(NZB: forall b0, In b0 (b::B) -> (bq b0)>0)
(NZA: forall a0, In a0 (a::A) -> (sq a0)>0):
(tb < bq b)/\(ta < sq a) -> 
(forall m, In m ((MM_aux (b::B) (a::A) tb ta)) -> tq m >0).
Proof. intros. destruct H. funelim (MM_aux (b::B) (a::A) tb ta).
rewrite <- Heqcall in H5. destruct (Nat.leb a b) eqn:Hab.
destruct (Nat.eqb (bq b - tb) (sq a - ta)) eqn:Heq.
{ destruct H5. subst m. simpl. lia. 
  destruct l. case l0 eqn:Hl0. simpl in H5. elim H5.
  simp MM_aux in H5. elim H5. case l0 eqn:Hl0. 
  simp MM_aux in H5. elim H5. apply H in H5. all:auto. 
  apply NZB. auto. apply NZA. auto.
}
{  destruct (Nat.leb (bq b - tb) (sq a - ta)) eqn:Hle.
   { destruct H5. subst m. simpl. lia. 
  destruct l.
  simp MM_aux in H5. elim H5. apply H0 in H5. all:auto. 
  apply NZB. auto. move /leP in Hle. 
  move /eqP in Heq. lia.
   }
   { destruct H5. subst m. simpl. lia. 
  destruct l0.
  simp MM_aux in H5. elim H5. apply H1 in H5. all:auto. 
  move /leP in Hle. lia. apply NZA. auto.
   }
 }
 {   destruct l0.
  simp MM_aux in H5. elim H5. apply H2 in H5. all:auto. 
  apply NZA. auto.
 } Qed.
 
Lemma MM_NZT (B:list Bid)(A:list Ask)
(NZB: forall b, In b B -> (bq b)>0)
(NZA: forall a, In a A -> (sq a)>0):
(forall m, In m ((MM_aux B A 0 0)) -> tq m >0).
Proof. destruct B. simp MM_aux. simpl. 
intros. elim H. destruct A. simp MM_aux.
simpl. intros. elim H. 
apply MM_aux_NZT with (b:=b)(a:=a).
all:auto. split. apply NZB. auto. apply NZA. auto. Qed.

 
Theorem MM_Is_IR_Matching (B:list Bid)(A:list Ask)
(NZB: forall b, In b B -> (bq b)>0)
(NZA: forall a, In a A -> (sq a)>0)
(NDA:NoDup (idas_of A))
(NDB:NoDup (idbs_of B)):
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
(NZT: forall m : fill_type, In m M -> tq m > 0):
Sorted by_dbp B ->
Sorted by_dsp A ->
matching_in B A M /\ Is_IR M->
QM((MM B A))>=QM(M).
Proof. intros.
       assert(HA:(sort by_dsp A) = A).
       { 
        apply sort_equal_nodup. apply by_dsp_refl. apply by_dsp_antisymmetric.
        all: auto. 
       }
       assert(HB:(sort by_dbp B)  = B).
       {
        apply sort_equal_nodup. apply by_dbp_refl. apply by_dbp_antisymmetric.
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


Theorem MM_FAIR_correct (B:list Bid)(A:list Ask)
(NZB: forall b, In b B -> (bq b)>0)
(NZA: forall a, In a A -> (sq a)>0)
(NDA:NoDup (idas_of A))
(NDB:NoDup (idbs_of B)):
Is_fair (MM_FAIR B A) B A.
Proof. apply FAIR_is_fair. all:auto. 
       apply MM_NZT. eauto. eauto.
       apply MM_Is_Matching.
       all:auto. Qed.

End MM_Process.


