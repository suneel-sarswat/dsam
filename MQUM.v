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
(UM_aux (sort by_dbp B) (sort by_sp A) 0 0) (uniform_price (sort by_dbp B) (sort by_sp A)).




          
(*Bellow three lemmas can be moved to lower level*)
Lemma idb_sort (B:list Bid): 
NoDup (idbs_of B) -> NoDup (idbs_of (sort by_dbp B)).
Proof. assert(perm (idbs_of B) (idbs_of (sort by_dbp B))). apply idb_perm.
eauto. intros. eapply perm_nodup. eauto. eauto. Qed.


Lemma ida_sort (A:list Ask): 
NoDup (idas_of A) -> NoDup (idas_of (sort by_sp A)).
Proof. assert(perm (idas_of A) (idas_of (sort by_sp A))). apply ida_perm.
eauto. intros. eapply perm_nodup. eauto. eauto. Qed.

Lemma fair_sort (M:list fill_type)(B:list Bid)(A:list Ask):
Is_fair M (sort by_dbp B) (sort by_sp A) -> Is_fair M B A.
Proof. unfold Is_fair. unfold fair_on_asks. unfold fair_on_bids.
intros. destruct H. split. intros. split. apply H in H2.
apply H2. destruct H1. split. eauto. eauto. auto. auto.
apply H in H2.
apply H2. destruct H1. split. eauto. eauto. auto. auto.
intros. split. apply H0 in H2.
apply H2. destruct H1. split. eauto. eauto. auto. auto.
apply H0 in H2.
apply H2. destruct H1. split. eauto. eauto. auto. auto. Qed.
 


(*Following Theorem says the The processs UM is Individual Rational 
and Uniform matching. Note that Is_uniform is defined as IR 
and Uniform matching*)
Theorem UM_Is_Uniform (B:list Bid)(A:list Ask)
(NZB: forall b, In b B -> (bq b)>0)
(NZA: forall a, In a A -> (sq a)>0)
(NDA:NoDup (idas_of A))
(NDB:NoDup (idbs_of B))
(Hanti: (antisymmetric by_sp)/\(antisymmetric by_dbp)):
Is_uniform (UM B A) B A.
Proof. intros. intros. assert(HA:Sorted by_sp (sort by_sp A)).
       apply sort_correct. apply by_sp_P. apply by_sp_P.
       intros. assert(HB:Sorted by_dbp (sort by_dbp B)).
       apply sort_correct. apply by_dbp_P. apply by_dbp_P.
       split. 
               { unfold UM. apply replace_column_is_uniform. }
               { split.
                 { split. 
                    { split. 
                      { unfold All_matchable. intros.
                         eapply UM_aux_is_Ind_Rat with (B:=(sort by_dbp B)) in HA.
                        unfold Is_IR in HA. unfold UM in H. apply HA in H.
                        unfold rational in H. lia. auto.
                      }
                      { split.
                       { intros. unfold UM.
                         replace (ttqb (replace_column
                         (UM_aux (sort by_dbp B) (sort by_sp A) 0 0)
                         (uniform_price (sort by_dbp B) (sort by_sp A))) b) with 
                         (ttqb (UM_aux (sort by_dbp B) (sort by_sp A) 0 0) b).
                         apply UM_aux_ttqb. apply idb_sort.
                         auto. apply ida_sort. auto.
                         apply replace_column_ttqb.
                       }
                       { intros. unfold UM.
                         replace (ttqa (replace_column
                         (UM_aux (sort by_dbp B) (sort by_sp A) 0 0)
                          (uniform_price (sort by_dbp B) (sort by_sp A))) a) with 
                          (ttqa (UM_aux (sort by_dbp B) (sort by_sp A) 0 0) a).
                         apply UM_aux_ttqa. apply idb_sort.
                         auto. apply ida_sort. auto. 
                         apply replace_column_ttqa.
                       } 
                     }
                   }
                   { split. unfold UM.
                     replace (bids_of (replace_column
                     (UM_aux (sort by_dbp B) (sort by_sp A) 0 0)
                     (uniform_price (sort by_dbp B) (sort by_sp A)))) with 
                     (bids_of (UM_aux (sort by_dbp B) (sort by_sp A) 0 0)). 
                     assert(bids_of (UM_aux (sort by_dbp B) 
                     (sort by_sp A) 0 0) [<=] (sort by_dbp B)).
                     apply UM_aux_subset_bidsB. eauto.
                     apply replace_column_bids.
                     unfold UM.
                     replace (asks_of (replace_column
                     (UM_aux (sort by_dbp B) (sort by_sp A) 0 0)
                     (uniform_price (sort by_dbp B) (sort by_sp A)))) with 
                     (asks_of (UM_aux (sort by_dbp B) (sort by_sp A) 0 0)). 
                     assert(asks_of (UM_aux (sort by_dbp B) 
                     (sort by_sp A) 0 0) [<=] (sort by_sp A)).
                     apply UM_aux_subset_asksA. eauto.
                     apply replace_column_asks.
                   }
                }
                { eapply UM_aux_is_Ind_Rat with (B:=(sort by_dbp B)) in HA.
                  auto. auto. 
                }
             }
          Qed.

(*This Theorem says that UM is fair matching.*)
Theorem UM_FAIR (B:list Bid)(A:list Ask)
(NZB: forall b, In b B -> (bq b)>0)
(NZA: forall a, In a A -> (sq a)>0)
(NDA:NoDup (idas_of A))
(NDB:NoDup (idbs_of B))
(Hanti: (antisymmetric by_sp)/\(antisymmetric by_dbp)):
Is_fair (UM B A) B A.
Proof.  assert(HA:Sorted by_sp (sort by_sp A)).
                        apply sort_correct. apply by_sp_P. apply by_sp_P.
                        intros. assert(HB:Sorted by_dbp (sort by_dbp B)).
                        apply sort_correct. apply by_dbp_P. apply by_dbp_P.
                        unfold UM. 
                        assert(Is_fair (UM_matching (sort by_dbp B) (sort by_sp A)) 
                        (sort by_dbp B) (sort by_sp A)). eapply UM_Fair. apply idb_sort.
                         auto. apply ida_sort. auto.
                        auto. auto. unfold UM_matching in H.
                        apply fair_sort in H. auto.
Qed.

(*This Theorem says that UM is maximum amongst all the uniform matchings*)

Theorem UM_Maximum (B:list Bid)(A:list Ask)(M:list fill_type)
(NZB: forall b, In b B -> (bq b)>0)
(NZA: forall a, In a A -> (sq a)>0)
(NDA:NoDup (idas_of A))
(NDB:NoDup (idbs_of B))
(NZT: forall m : fill_type, In m M -> tq m > 0)
(Hanti: (antisymmetric by_sp)/\(antisymmetric by_dbp)):
Is_uniform M B A ->
QM((UM B A))>=QM(M).
Proof.  unfold UM. intros.
        replace (QM (replace_column
        (UM_aux (sort by_dbp B) (sort by_sp A) 0 0)
        (uniform_price (sort by_dbp B) (sort by_sp A))))
        with (QM (UM_aux (sort by_dbp B) (sort by_sp A) 0 0)).
        apply UM_aux_optimal. 
        all: auto. eauto. eauto. apply ida_sort. auto.
        apply idb_sort. auto. apply sort_correct.
        apply by_dbp_P. apply by_dbp_P.
        apply sort_correct. apply by_sp_P. apply by_sp_P.
        split. apply H. split. destruct H. destruct H0.
        apply match_inv with (M':=M)(B':=(sort by_dbp B))(A':=(sort by_sp A)) in H0.
        auto. auto. eauto. eauto. apply H.
        eapply replace_column_size. 
Qed.

End UM_Process.



