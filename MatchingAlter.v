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

Section Transform.

Definition Is_uniform M B A := (Uniform M /\ matching_in B A M /\ Is_IR M).
(*########UM Surgery for Q(b,a,M')  = Q(b,a,M) + 1 matching ############*)

(*This function g_increase_top takes two transactions ma and mb of M, where ask of ma is a and bid of mb is b. It reduces the trades quantity of ma and mb by 1 and inserts two transactions of single quantity between a <--> b and between partners if a and b. This is used in the proofs maximality for MM and UM. 
Here we proves correctness properties of g_increase_top.*)


Definition g_increase_top (M:list fill_type)(mb ma:fill_type)(b:Bid)(a:Ask):(list fill_type):=
    if (Nat.eqb (tq ma) 1) 
    then 
        (
        if (Nat.eqb (tq mb) 1) 
        then
            (Mk_fill b a 1 (tp ma))::(Mk_fill (bid_of ma) (ask_of mb) 1 (tp ma))::
            (delete mb (delete ma M))
        else
            (Mk_fill b a 1 (tp ma))::(Mk_fill (bid_of ma) (ask_of mb) 1 (tp ma))::
            (Mk_fill (bid_of mb) (ask_of mb) (tq mb - 1)  (tp ma))::
            (delete mb (delete ma M))
        )
    else
        (
        if (Nat.eqb (tq mb) 1) 
        then
            (Mk_fill b a 1 (tp ma))::(Mk_fill (bid_of ma) (ask_of mb) 1 (tp ma))::
            (Mk_fill (bid_of ma) (ask_of ma) (tq ma - 1)  (tp ma))::
            (delete mb (delete ma M))
        else
            (Mk_fill b a 1 (tp ma))::(Mk_fill (bid_of ma) (ask_of mb) 1 (tp ma))::
            (Mk_fill (bid_of ma) (ask_of ma) (tq ma - 1)  (tp ma))::
            (Mk_fill (bid_of mb) (ask_of mb) (tq mb - 1)  (tp mb))::
            (delete mb (delete ma M))
         ).
(*Proof that total size of matching is not changed *)
Lemma g_increase_top_size (M:list fill_type)(m1 m2:fill_type)(b:Bid)(a:Ask)
(NZT:(forall m, In m M -> (tq m) > 0)):
In m1 M ->
In m2 M ->
m1<>m2 ->
QM(M) = QM(g_increase_top M m1 m2 b a).
Proof. unfold g_increase_top. intros. 
       assert(Hdel:forall M m, In m M -> QM(delete m M) =QM(M) - (tq m)).
       intros. eauto.
       assert(QM(M) >= (tq m1) + (tq m2)).
       apply QM_elim2. all:auto.
       assert (Hm1in: In m1 (delete m2 M)). eapply delete_intro.
       all:auto.
       destruct (Nat.eqb (tq m2) 1) eqn:Hm1.
       { destruct (Nat.eqb (tq m1) 1) eqn:Hm2.
         { simpl. eapply Hdel in Hm1in.
           rewrite Hm1in. eapply Hdel in H0. rewrite H0.
           move /eqP in Hm1. move /eqP in Hm2. lia.
         }
         { simpl. eapply Hdel in Hm1in.
           rewrite Hm1in. eapply Hdel in H0. rewrite H0.
           move /eqP in Hm1. move /eqP in Hm2. assert(tq m1 > 0). 
           apply NZT. auto.  lia.
         }
       }
       { destruct (Nat.eqb (tq m1) 1) eqn:Hm2.
         { simpl. eapply Hdel in Hm1in.
           rewrite Hm1in. eapply Hdel in H0 as H01. rewrite H01.
           move /eqP in Hm1. move /eqP in Hm2. assert(tq m2 > 0). 
           apply NZT. auto.  lia.
         }
         { simpl. eapply Hdel in Hm1in.
           rewrite Hm1in. eapply Hdel in H0 as H01. rewrite H01.
           move /eqP in Hm1. move /eqP in Hm2. 
           assert(tq m1 > 0). apply NZT. auto. 
           assert(tq m2 > 0). apply NZT. auto.  lia.
         }
       } Qed.
(*Proof that all the transactions of g are non-zero*)
Lemma g_increase_top_NZT (M:list fill_type)(m1 m2:fill_type)(b:Bid)(a:Ask)
(NZT:(forall m, In m M -> (tq m) > 0)):
In m1 M ->
In m2 M ->
((forall m, In m (g_increase_top M m1 m2 b a) -> (tq m) > 0)).
Proof. unfold g_increase_top. intros.  
       destruct (Nat.eqb (tq m2) 1) eqn:Hm1.
       { destruct (Nat.eqb (tq m1) 1) eqn:Hm2.
         { simpl in H1. destruct H1. subst m. simpl. lia. 
           destruct H1.  subst m.  simpl.  lia. 
           apply NZT.  eapply delete_elim1 with (b0:=m2). 
            eapply delete_elim1 with (b0:=m1). auto.
         }
         { simpl in H1. destruct H1. subst m. simpl. lia. 
           destruct H1.  subst m.  simpl.  lia.
           destruct H1.  subst m.  simpl. 
           move /eqP in Hm2. assert(tq m1 > 0). 
           apply NZT. auto.  lia. 
           apply NZT.  eapply delete_elim1 with (b0:=m2). 
            eapply delete_elim1 with (b0:=m1). auto.
         }
       }
       { destruct (Nat.eqb (tq m1) 1) eqn:Hm2.
         { simpl in H1. destruct H1. subst m. simpl. lia. 
           destruct H1.  subst m.  simpl.  lia. 
           destruct H1.  subst m.  simpl. 
           move /eqP in Hm1. assert(tq m2 > 0). 
           apply NZT. auto.  lia. 
           apply NZT.  eapply delete_elim1 with (b0:=m2). 
            eapply delete_elim1 with (b0:=m1). auto.
         }
         { simpl in H1. destruct H1. subst m. simpl. lia. 
           destruct H1.  subst m.  simpl.  lia.
           destruct H1.  subst m.  simpl. 
           move /eqP in Hm1. assert(tq m2 > 0). 
           apply NZT. auto.  lia.
           destruct H1.  subst m.  simpl. 
           move /eqP in Hm2. assert(tq m1 > 0). 
           apply NZT. auto.   lia. 
           apply NZT.  eapply delete_elim1 with (b0:=m2). 
            eapply delete_elim1 with (b0:=m1). auto.
         }
       } Qed.

(*Proof that in g, the trade between a and b is increased by single unit.*)

Lemma g_increase_top_trade_equal (M:list fill_type)(m1 m2:fill_type)(b:Bid)(a:Ask)
(NZT:(forall m, In m M -> (tq m) > 0)):
In m1 M ->
In m2 M ->
m1<>m2 ->
a=ask_of m1 ->
b<> bid_of m1 ->
b=bid_of m2 ->
a<>ask_of m2 ->
ttq_ab (g_increase_top M m2 m1 b a) b a= 1 + ttq_ab M b a.
Proof.
 unfold g_increase_top. intros.  
       destruct (Nat.eqb (tq m2) 1) eqn:Hm1.
       { destruct (Nat.eqb (tq m1) 1) eqn:Hm2.
         { simpl. replace (a_eqb a a) with true.
           replace (b_eqb b b) with true. simpl. 
           replace (a_eqb a (ask_of m2)) with false. 
           replace (b_eqb b (bid_of m1)) with false.
           simpl. replace (ttq_ab M b a) with (ttq_ab (delete m1 M) b a).
           replace (ttq_ab (delete m1 M) b a) with (ttq_ab (delete m2 (delete m1 M)) b a).
           auto. symmetry. eapply ttq_ab_delete with (M:=(delete m1 M)).
           eapply delete_intro. auto. auto. auto. symmetry.
           eapply ttq_ab_delete. auto. auto. 
           destruct (b_eqb b (bid_of m1)) eqn: Hbm1.
           move /eqP in Hbm1. subst b. elim H3. auto. auto.
           destruct (a_eqb a (ask_of m2)) eqn: Hbm2.
           move /eqP in Hbm2. subst a. elim H5. auto. auto.
           eauto. eauto.
         }
         { simpl. replace (a_eqb a a) with true.
           replace (b_eqb b b) with true. simpl. 
           replace (a_eqb a (ask_of m2)) with false. 
           replace (b_eqb b (bid_of m1)) with false.
           simpl. replace (a_eqb a (ask_of m1)) with true. simpl.
           replace (ttq_ab M b a) with (ttq_ab (delete m1 M) b a).
           replace (ttq_ab (delete m1 M) b a) with (ttq_ab (delete m2 (delete m1 M)) b a).
           auto. symmetry. eapply ttq_ab_delete with (M:=(delete m1 M)).
           eapply delete_intro. auto. auto. auto. symmetry.
           eapply ttq_ab_delete. auto. auto. 
           destruct (b_eqb b (bid_of m1)) eqn: Hbm1.
           move /eqP in Hbm1. subst b. elim H3. auto. auto.
           destruct (a_eqb a (ask_of m2)) eqn: Hbm2.
           move /eqP in Hbm2. subst a. elim H5. auto. auto.
           destruct (a_eqb a (ask_of m2)) eqn: Hbm2.
           move /eqP in Hbm2. subst a. elim H5. auto. auto.
           eauto. eauto.
         }
       }
       { destruct (Nat.eqb (tq m1) 1) eqn:Hm2.
         { simpl. replace (a_eqb a a) with true.
           replace (b_eqb b b) with true. simpl. 
           replace (a_eqb a (ask_of m2)) with false. 
           replace (b_eqb b (bid_of m1)) with false.
           simpl. replace (a_eqb a (ask_of m1)) with true. simpl.
           replace (ttq_ab M b a) with (ttq_ab (delete m1 M) b a).
           replace (ttq_ab (delete m1 M) b a) with (ttq_ab (delete m2 (delete m1 M)) b a).
           auto. symmetry. eapply ttq_ab_delete with (M:=(delete m1 M)).
           eapply delete_intro. auto. auto. auto. symmetry.
           eapply ttq_ab_delete. auto. auto. 
           destruct (b_eqb b (bid_of m1)) eqn: Hbm1.
           move /eqP in Hbm1. subst b. elim H3. auto. auto.
           destruct (a_eqb a (ask_of m2)) eqn: Hbm2.
           move /eqP in Hbm2. subst a. elim H5. auto. auto.
           destruct (a_eqb a (ask_of m2)) eqn: Hbm2.
           move /eqP in Hbm2. subst a. elim H5. auto. auto.
           eauto. eauto.
         }
         { simpl. replace (a_eqb a a) with true.
           replace (b_eqb b b) with true. simpl. 
           replace (a_eqb a (ask_of m2)) with false. 
           replace (b_eqb b (bid_of m1)) with false.
           simpl. replace (a_eqb a (ask_of m1)) with true. simpl.
           replace (ttq_ab M b a) with (ttq_ab (delete m1 M) b a).
           replace (ttq_ab (delete m1 M) b a) with (ttq_ab (delete m2 (delete m1 M)) b a).
           auto. symmetry. eapply ttq_ab_delete with (M:=(delete m1 M)).
           eapply delete_intro. auto. auto. auto. symmetry.
           eapply ttq_ab_delete. auto. auto. 
           destruct (b_eqb b (bid_of m1)) eqn: Hbm1.
           move /eqP in Hbm1. subst b. elim H3. auto. auto.
           destruct (a_eqb a (ask_of m2)) eqn: Hbm2.
           move /eqP in Hbm2. subst a. elim H5. auto. auto.
           destruct (a_eqb a (ask_of m2)) eqn: Hbm2.
           move /eqP in Hbm2. subst a. elim H5. auto. auto.
           eauto. eauto.
         }

       } Qed.

(*Proof that trade fill of bid b is invariant in g*)
Lemma g_increase_top_bqb_equal (M:list fill_type)(m1 m2:fill_type)(b:Bid)(a:Ask)
(NZT:(forall m, In m M -> (tq m) > 0)):
In m1 M ->
In m2 M ->
m1<>m2 ->
b=bid_of m2 ->
ttqb (g_increase_top M m2 m1 b a) b = ttqb M b.
Proof.
 unfold g_increase_top. intros.  
       destruct (Nat.eqb (tq m2) 1) eqn:Hm1.
       move /eqP in Hm1.
       { destruct (Nat.eqb (tq m1) 1) eqn:Hm2.
         { move /eqP in Hm2.
           simpl. replace (b_eqb b b) with true.  
           destruct (b_eqb b (bid_of m1)) eqn: Hbm1.
           { 
             move /eqP in Hbm1. replace (ttqb M b) with 
             (ttqb (delete m1 M) b + tq m1).
             replace (ttqb (delete m1 M) b) with 
             (ttqb (delete m2 (delete m1 M)) b + tq m2).
             lia. symmetry. eauto. symmetry. eauto.
           }
           {
             move /eqP in Hbm1. replace (ttqb M b) with 
             (ttqb (delete m1 M) b).
             replace (ttqb (delete m1 M) b) with 
             (ttqb (delete m2 (delete m1 M)) b + tq m2).
             lia. symmetry. eauto. symmetry. eauto.           
           }
           eauto.
         }
         { move /eqP in Hm2.
           simpl. replace (b_eqb b b) with true.  
           destruct (b_eqb b (bid_of m1)) eqn: Hbm1.
           { 
             move /eqP in Hbm1. replace (ttqb M b) with 
             (ttqb (delete m1 M) b + tq m1).
             replace (ttqb (delete m1 M) b) with 
             (ttqb (delete m2 (delete m1 M)) b + tq m2).
             assert(tq m1 > 0). auto.
             lia. symmetry. eauto. symmetry. eauto.
           }
           {
             move /eqP in Hbm1. replace (ttqb M b) with 
             (ttqb (delete m1 M) b).
             replace (ttqb (delete m1 M) b) with
             (ttqb (delete m2 (delete m1 M)) b + tq m2).
             lia. symmetry. eauto. symmetry. eauto.           
           }
           eauto.
         }
       }
       { destruct (Nat.eqb (tq m1) 1) eqn:Hm2.
         { move /eqP in Hm2.
           simpl. replace (b_eqb b b) with true.  
           destruct (b_eqb b (bid_of m1)) eqn: Hbm1.
           { 
             move /eqP in Hbm1. 
             destruct (b_eqb b (bid_of m2)) eqn: Hbm2.
             assert(tq m2 > 0). auto.
             replace (ttqb M b) with 
             (ttqb (delete m1 M) b + tq m1).
             replace (ttqb (delete m1 M) b) with 
             (ttqb (delete m2 (delete m1 M)) b + tq m2).
             lia. symmetry. eauto. symmetry. eauto.
             move /eqP in Hbm2. subst b. elim Hbm2. auto.
           }
           {
             move /eqP in Hbm1. 
             destruct (b_eqb b (bid_of m2)) eqn: Hbm2.
             assert(tq m2 > 0). auto.
             replace (ttqb M b) with (ttqb (delete m1 M) b).
             replace (ttqb (delete m1 M) b) with 
             (ttqb (delete m2 (delete m1 M)) b + tq m2).
             lia. symmetry. eauto. symmetry. eauto.
             move /eqP in Hbm2. subst b. elim Hbm2.
             auto.                        
           }
           eauto.
         }
         {  move /eqP in Hm2.
           simpl. replace (b_eqb b b) with true.  
           destruct (b_eqb b (bid_of m1)) eqn: Hbm1.
           { 
             move /eqP in Hbm1. 
             destruct (b_eqb b (bid_of m2)) eqn: Hbm2.
             assert(tq m2 > 0). auto.
             assert(tq m1 > 0). auto.
             replace (ttqb M b) with (ttqb (delete m1 M) b + tq m1).
             replace (ttqb (delete m1 M) b) with 
             (ttqb (delete m2 (delete m1 M)) b + tq m2).
             lia. symmetry. eauto. symmetry. eauto.
             move /eqP in Hbm2. subst b. elim Hbm2. auto.
           }
           {
             move /eqP in Hbm1. 
             destruct (b_eqb b (bid_of m2)) eqn: Hbm2.
             assert(tq m2 > 0). auto.
             assert(tq m1 > 0). auto.
             replace (ttqb M b) with (ttqb (delete m1 M) b).
             replace (ttqb (delete m1 M) b) with 
             (ttqb (delete m2 (delete m1 M)) b + tq m2).
             lia. symmetry. eauto. symmetry. eauto.
             move /eqP in Hbm2. subst b. elim Hbm2.
             auto.                        
           }
           eauto.
         }
      } Qed.

(*Proof that trade fill of ask a is invariant in g*)
Lemma g_increase_top_sqa_equal (M:list fill_type)(m1 m2:fill_type)(b:Bid)(a:Ask)
(NZT:(forall m, In m M -> (tq m) > 0)):
In m1 M ->
In m2 M ->
m1<>m2 ->
a=ask_of m1 ->
ttqa (g_increase_top M m2 m1 b a) a = ttqa M a.
Proof.
 unfold g_increase_top. intros.  
       destruct (Nat.eqb (tq m2) 1) eqn:Hm1.
       move /eqP in Hm1.
       { destruct (Nat.eqb (tq m1) 1) eqn:Hm2.
         { move /eqP in Hm2.
           simpl. replace (a_eqb a a) with true.  
           destruct (a_eqb a (ask_of m2)) eqn: Ham2.
           { 
             move /eqP in Ham2. replace (ttqa M a) with 
             (ttqa (delete m1 M) a + tq m1).
             replace (ttqa (delete m1 M) a) with 
             (ttqa (delete m2 (delete m1 M)) a + tq m2).
             lia. symmetry. eauto. symmetry. eauto.
           }
           {
             move /eqP in Ham2. replace (ttqa M a) with 
             (ttqa (delete m1 M) a + tq m1).
             replace (ttqa (delete m1 M) a) with (ttqa 
             (delete m2 (delete m1 M)) a).
             lia. symmetry. eauto. symmetry. eauto.           
           }
           eauto.
         }
         { move /eqP in Hm2.
           simpl. replace (a_eqb a a) with true.  
           simpl. destruct (a_eqb a (ask_of m2)) eqn: Ham2.
           { 
             move /eqP in Ham2. 
             destruct (a_eqb a (ask_of m1)) eqn: Ham1.
             assert(tq m1 > 0). auto.
             replace (ttqa M a) with (ttqa (delete m1 M) a + tq m1).
             replace (ttqa (delete m1 M) a) with 
             (ttqa (delete m2 (delete m1 M)) a + tq m2).
             lia. symmetry. eauto. symmetry. eauto.
             move /eqP in Ham1. subst a. elim Ham1. auto.
           }
           {
             move /eqP in Ham2. 
             destruct (a_eqb a (ask_of m1)) eqn: Ham1.
             assert(tq m1 > 0). auto.
             replace (ttqa M a) with (ttqa (delete m1 M) a + tq m1).
             replace (ttqa (delete m1 M) a) with 
             (ttqa (delete m2 (delete m1 M)) a).
             lia. symmetry. eauto. symmetry. eauto.
             move /eqP in Ham1. subst a. elim Ham1.
             auto.                        
           }

          eauto.
         }
       }
       {  destruct (Nat.eqb (tq m1) 1) eqn:Hm2.
           move /eqP in Hm1.
           simpl. replace (a_eqb a a) with true.  
           destruct (a_eqb a (ask_of m2)) eqn: Ham2.
           { 
             move /eqP in Ham2. replace (ttqa M a) with 
             (ttqa (delete m1 M) a + tq m1).
             replace (ttqa (delete m1 M) a) with 
             (ttqa (delete m2 (delete m1 M)) a + tq m2).
             assert(tq m2 > 0). auto. move /eqP in Hm2.
             lia. symmetry. eauto. symmetry. eauto.
           }
           {
             move /eqP in Ham2. replace (ttqa M a) with 
             (ttqa (delete m1 M) a + tq m1).
             replace (ttqa (delete m1 M) a) with 
             (ttqa (delete m2 (delete m1 M)) a).
             move /eqP in Hm2. lia. symmetry. eauto. symmetry.
             eauto.           
           }

           eauto.
         {
             assert(tq m2 > 0). auto.
             assert(tq m1 > 0). auto.
             move /eqP in Hm1. move /eqP in Hm2.
             simpl. replace (a_eqb a a) with true. 
             destruct (a_eqb a (ask_of m2)) eqn: Ham2.
             {
               move /eqP in Ham2. 
               destruct (a_eqb a (ask_of m1)) eqn: Ham1.
               replace (ttqa M a) with (ttqa (delete m1 M) a + tq m1).
               replace (ttqa (delete m1 M) a) with 
               (ttqa (delete m2 (delete m1 M)) a + tq m2).
               lia. symmetry. eauto. symmetry. eauto.
               move /eqP in Ham1. subst a. elim Ham1. auto.
             }
             {               
               move /eqP in Ham2. 
               destruct (a_eqb a (ask_of m1)) eqn: Ham1.
               replace (ttqa M a) with (ttqa (delete m1 M) a + tq m1).
               replace (ttqa (delete m1 M) a) with 
               (ttqa (delete m2 (delete m1 M)) a).
               lia. symmetry. eauto. symmetry. eauto.
               move /eqP in Ham1. subst a. elim Ham1. auto.
             }
           eauto.
         }
      } Qed.
      
      
Lemma g_increase_top_matching_IR (M:list fill_type)(m1 m2:fill_type)(b:Bid)(a:Ask)
(NZT:(forall m, In m M -> (tq m) > 0)):
In m1 M ->
In m2 M ->
Is_IR M ->
b=bid_of m2 ->
a=ask_of m1 ->
b>= a ->
a>= ask_of m2 ->
b>= bid_of m1 ->
All_matchable M ->
Is_IR (g_increase_top M m2 m1 b a).
Proof. unfold Is_IR. unfold All_matchable.
       unfold g_increase_top. unfold rational. 
       intros.
       apply H1 in H as Hm1p.
       apply H1 in H0 as Hm2p.
(*       assert(tp m1 = tp m2). eauto.*)
       destruct (Nat.eqb (tq m2) 1) eqn:Hm1.
       { destruct (Nat.eqb (tq m1) 1) eqn:Hm2.
         { simpl in H8. 
           destruct H8. subst m. 
           simpl. subst. lia. destruct H8. subst m. 
           simpl. subst. lia. eauto.
         }
         { simpl in H8. 
           destruct H8. subst m. simpl. subst. lia. 
           destruct H8. subst m. simpl. subst. lia. 
           destruct H8. subst m. simpl. subst. lia. 
           eauto.
         }
       }
       { destruct (Nat.eqb (tq m1) 1) eqn:Hm2.
         { simpl in H8. 
           destruct H8. subst m. simpl. subst. lia. 
           destruct H8. subst m. simpl. subst. lia. 
           destruct H8. subst m. simpl. subst. lia. 
           eauto.
         }
         { simpl in H8. 
           destruct H8. subst m. simpl. subst. lia. 
           destruct H8. subst m. simpl. subst. lia.
           destruct H8. subst m. simpl. subst. lia.
           destruct H8. subst m. simpl. subst. lia.
           eauto.
         }
       } Qed.


Lemma g_increase_top_IR (M:list fill_type)(m1 m2:fill_type)(b:Bid)(a:Ask)
(NZT:(forall m, In m M -> (tq m) > 0)):
In m1 M ->
In m2 M ->
Is_IR M ->
b=bid_of m2 ->
a=ask_of m1 ->
Uniform M ->
Is_IR (g_increase_top M m2 m1 b a).
Proof. unfold Is_IR. unfold g_increase_top. unfold rational. 
       unfold Uniform. intros.
       apply H1 in H as Ha. apply H1 in H0 as Hb.
       assert(tp m1 = tp m2). eauto.
       destruct (Nat.eqb (tq m2) 1) eqn:Hm1.
       { destruct (Nat.eqb (tq m1) 1) eqn:Hm2.
         { simpl in H5. 
           destruct H5. subst m. 
           simpl. subst. lia. destruct H5. subst m. 
           simpl. lia. eauto.
         }
         { simpl in H5. 
           destruct H5. subst m. simpl. subst. lia. 
           destruct H5. subst m. simpl. lia. 
           destruct H5. subst m. simpl. lia. 
           eauto.
         }
       }
       { destruct (Nat.eqb (tq m1) 1) eqn:Hm2.
         { simpl in H5. 
           destruct H5. subst m. simpl. subst. lia. 
           destruct H5. subst m. simpl. lia. 
           destruct H5. subst m. simpl. lia. 
           eauto.
         }
         { simpl in H5. 
           destruct H5. subst m. simpl. subst. lia. 
           destruct H5. subst m. simpl. lia. 
           destruct H5. subst m. simpl. lia. 
           destruct H5. subst m. simpl. lia. 
           eauto.
         }
       } Qed.


Lemma g_increase_top_Uniform (M:list fill_type)(m1 m2:fill_type)(b:Bid)(a:Ask):
In m1 M ->
In m2 M ->
Uniform M ->
Uniform (g_increase_top M m2 m1 b a).
Proof. unfold g_increase_top. unfold Uniform. intros.
       assert(tp m1 = tp m2). eauto.
       destruct (Nat.eqb (tq m2) 1) eqn:Hm1.
       { destruct (Nat.eqb (tq m1) 1) eqn:Hm2.
         { simpl. constructor. auto. apply uniform_intro.
           intros. assert(In x (trade_prices_of M)).
           apply tps_of_delete in H3. 
           apply tps_of_delete in H3.
           exact. assert(In (tp m1) (trade_prices_of M)).
           eauto. apply uniform_elim4 with (a1:=x)(a2:=tp m1) in H1.
           auto. auto. auto.
         }
         { simpl. constructor. auto. constructor.  auto. 
           apply uniform_intro.
           intros. assert(In x (trade_prices_of M)).
           apply tps_of_delete in H3. 
           apply tps_of_delete in H3.
           exact. assert(In (tp m1) (trade_prices_of M)).
           eauto. apply uniform_elim4 with (a1:=x)(a2:=tp m1) in H1.
           auto. auto. auto.
         }
       }
       { destruct (Nat.eqb (tq m1) 1) eqn:Hm2.
         { simpl. constructor. auto. constructor. auto. 
           apply uniform_intro.
           intros. assert(In x (trade_prices_of M)).
           apply tps_of_delete in H3. 
           apply tps_of_delete in H3.
           exact. assert(In (tp m1) (trade_prices_of M)).
           eauto. apply uniform_elim4 with (a1:=x)(a2:=tp m1) in H1.
           auto. auto. auto.
         }
         { simpl. constructor. auto. 
           constructor. auto. constructor. auto.
           apply uniform_intro.
           intros. assert(In x (trade_prices_of M)).
           apply tps_of_delete in H3. 
           apply tps_of_delete in H3.
           exact. assert(In (tp m2) (trade_prices_of M)).
           eauto. apply uniform_elim4 with (a1:=x)(a2:=tp m2) in H1.
           auto. auto. auto.
         }
       } Qed.

Lemma g_increase_top_bids_subset (M:list fill_type)(m1 m2:fill_type)(b:Bid)(a:Ask):
In m1 M ->
In m2 M ->
b=bid_of m2 ->
a=ask_of m1 ->
bids_of (g_increase_top M m2 m1 b a) [<=] bids_of M.
Proof. unfold g_increase_top. intros.
       destruct (Nat.eqb (tq m2) 1) eqn:Hm1.
       { destruct (Nat.eqb (tq m1) 1) eqn:Hm2.
         { simpl. unfold "[<=]". intros. 
           simpl in H3. 
           destruct H3. subst. eauto. 
           destruct H3. subst. eauto. eauto.
         }
         { simpl. unfold "[<=]". intros. 
           simpl in H3. 
           destruct H3. subst. eauto. 
           destruct H3. subst. eauto. 
           destruct H3. subst. eauto. eauto.
         }
       }
       { destruct (Nat.eqb (tq m1) 1) eqn:Hm2.
         { simpl. unfold "[<=]". intros. 
           simpl in H3. 
           destruct H3. subst. eauto. 
           destruct H3. subst. eauto. 
           destruct H3. subst. eauto. eauto.
         }
         { simpl. unfold "[<=]". intros. 
           simpl in H3. 
           destruct H3. subst. eauto. 
           destruct H3. subst. eauto. 
           destruct H3. subst. eauto. 
           destruct H3. subst. eauto. eauto.
         }
       } Qed.
       
Lemma g_increase_top_asks_subset (M:list fill_type)(m1 m2:fill_type)(b:Bid)(a:Ask):
In m1 M ->
In m2 M ->
b=bid_of m2 ->
a=ask_of m1 ->
asks_of (g_increase_top M m2 m1 b a) [<=] asks_of M.
Proof. unfold g_increase_top. intros.
       destruct (Nat.eqb (tq m2) 1) eqn:Hm1.
       { destruct (Nat.eqb (tq m1) 1) eqn:Hm2.
         { simpl. unfold "[<=]". intros. 
           simpl in H3. 
           destruct H3. subst. eauto. 
           destruct H3. subst. eauto. eauto.
         }
         { simpl. unfold "[<=]". intros. 
           simpl in H3. 
           destruct H3. subst. eauto. 
           destruct H3. subst. eauto. 
           destruct H3. subst. eauto. eauto.
         }
       }
       { destruct (Nat.eqb (tq m1) 1) eqn:Hm2.
         { simpl. unfold "[<=]". intros. 
           simpl in H3. 
           destruct H3. subst. eauto. 
           destruct H3. subst. eauto. 
           destruct H3. subst. eauto. eauto.
         }
         { simpl. unfold "[<=]". intros. 
           simpl in H3. 
           destruct H3. subst. eauto. 
           destruct H3. subst. eauto. 
           destruct H3. subst. eauto. 
           destruct H3. subst. eauto. eauto.
         }
       } Qed.



Lemma g_increase_top_matchable (M:list fill_type)(m1 m2:fill_type)(b:Bid)(a:Ask)
(NZT:(forall m, In m M -> (tq m) > 0)):
In m1 M ->
In m2 M ->
Is_IR M ->
b=bid_of m2 ->
a=ask_of m1 ->
b>= a ->
a>= ask_of m2 ->
b>= bid_of m1 ->
All_matchable M ->
All_matchable (g_increase_top M m2 m1 b a).
Proof. intros. assert(Is_IR (g_increase_top M m2 m1 b a)). 
       apply g_increase_top_matching_IR. all:auto. 
       unfold Is_IR in H8. unfold rational in H8.  
       unfold All_matchable. intros.
       apply H8 in H9. lia. Qed.

Lemma g_increase_top_IR_matchable (M:list fill_type)(m1 m2:fill_type)(b:Bid)(a:Ask)
(NZT:forall m : fill_type, In m M -> tq m > 0):
In m1 M ->
In m2 M ->
Is_IR M ->
b=bid_of m2 ->
a=ask_of m1 ->
Uniform M ->
All_matchable (g_increase_top M m2 m1 b a).
Proof. intros. assert(Is_IR (g_increase_top M m2 m1 b a)). 
       apply g_increase_top_IR. all:auto. 
       unfold Is_IR in H5. unfold rational in H5.  
       unfold All_matchable. intros.
       specialize (H5 m). apply H5 in H6. lia. Qed.


Lemma g_increase_top_ttqb (M:list fill_type)(m1 m2:fill_type)(b b0:Bid)(a:Ask)
(NZT:forall m : fill_type, In m M -> tq m > 0):
In m1 M ->
In m2 M ->
b=bid_of m2 ->
a=ask_of m1 ->
m1<>m2 ->
ttqb (g_increase_top M m2 m1 b a) b0 = ttqb M b0.
Proof.
       destruct (b_eqb b0 b) eqn:Hbb0.
       { move /eqP in Hbb0. subst. intros.
         eapply g_increase_top_bqb_equal.
         all:auto.
       }
       {
       unfold g_increase_top. intros.  
       destruct (Nat.eqb (tq m2) 1) eqn:Hm1.
       move /eqP in Hm1.
       { destruct (Nat.eqb (tq m1) 1) eqn:Hm2.
         { move /eqP in Hm2.
           simpl. rewrite Hbb0.
           destruct (b_eqb b0 (bid_of m1)) eqn: Hb0m1.
           { 
             move /eqP in Hb0m1. replace (ttqb M b0) with 
             (ttqb (delete m1 M) b0 + tq m1).
             replace (ttqb (delete m1 M) b0) with 
             (ttqb (delete m2 (delete m1 M)) b0).
             lia. symmetry. apply ttqb_delete_m_not_ofb.
             apply delete_intro with (b1:=m1) in H0.
             auto. auto. subst. move /eqP in Hbb0.
             auto. symmetry. eauto.
           }
           {
             move /eqP in Hb0m1. replace (ttqb M b0) with 
             (ttqb (delete m1 M) b0).
             replace (ttqb (delete m1 M) b0) with 
             (ttqb (delete m2 (delete m1 M)) b0).
             lia. symmetry. apply ttqb_delete_m_not_ofb.
             apply delete_intro with (b1:=m1) in H0.
             auto. auto. move /eqP in Hbb0. subst.
             auto.
             symmetry. eauto.           
           }
         }
         { move /eqP in Hm2.
           simpl. rewrite Hbb0.
           destruct (b_eqb b0 (bid_of m1)) eqn: Hb0m1.
           { 
             move /eqP in Hb0m1. replace (ttqb M b0) with 
             (ttqb (delete m1 M) b0 + tq m1).
             replace (ttqb (delete m1 M) b0) with 
             (ttqb (delete m2 (delete m1 M)) b0).
             assert(tq m1 >0). auto. lia. 
             symmetry. apply ttqb_delete_m_not_ofb.
             apply delete_intro with (b1:=m1) in H0.
             auto. auto. subst. move /eqP in Hbb0.
             auto. symmetry. eauto.
           }
           {
             move /eqP in Hb0m1. replace (ttqb M b0) with 
             (ttqb (delete m1 M) b0).
             replace (ttqb (delete m1 M) b0) with 
             (ttqb (delete m2 (delete m1 M)) b0).
             lia. symmetry. apply ttqb_delete_m_not_ofb.
             apply delete_intro with (b1:=m1) in H0.
             auto. auto. move /eqP in Hbb0. subst.
             auto.
             symmetry. eauto.           
           }
         }
       }
       { destruct (Nat.eqb (tq m1) 1) eqn:Hm2.
         { move /eqP in Hm2.
           simpl.  rewrite Hbb0.
           destruct (b_eqb b0 (bid_of m1)) eqn: Hb0m1.
           { 
             move /eqP in Hb0m1. 
             destruct (b_eqb b0 (bid_of m2)) eqn: Hb0m2.
             move /eqP in Hb0m2. move /eqP in Hbb0.
             subst. auto. 
             assert(tq m2 > 0). auto.
             move /eqP in Hm1.
             replace (ttqb M b0) with 
             (ttqb (delete m1 M) b0 + tq m1).
             replace (ttqb (delete m1 M) b0) with 
             (ttqb (delete m2 (delete m1 M)) b0).
             lia. symmetry. move /eqP in Hb0m2. eauto. symmetry. eauto.
           }
           {
             move /eqP in Hb0m1. move /eqP in Hm1.
             destruct (b_eqb b0 (bid_of m2)) eqn: Hbm2.
             move /eqP in Hbm2. subst.
             move /eqP in Hbb0. elim Hbb0.  auto. 
             assert(tq m2 > 0). auto. move /eqP in Hbm2.
             replace (ttqb M b0) with (ttqb (delete m1 M) b0).
             replace (ttqb (delete m1 M) b0) with 
             (ttqb (delete m2 (delete m1 M)) b0).
             lia. symmetry. eauto. symmetry. eauto.
           }
         }
         {  move /eqP in Hm2.
           simpl. rewrite Hbb0.
           destruct (b_eqb b0 (bid_of m1)) eqn: Hbm1.
           { 
             move /eqP in Hbm1. move /eqP in Hm1.
             destruct (b_eqb b0 (bid_of m2)) eqn: Hbm2.
             move /eqP in Hbm2. subst.
             move /eqP in Hbb0. auto. 
             assert(tq m2 > 0). auto.
             assert(tq m1 > 0). auto.
             move /eqP in Hbm2.
             replace (ttqb M b0) with (ttqb (delete m1 M) b0 + tq m1).
             replace (ttqb (delete m1 M) b0) with 
             (ttqb (delete m2 (delete m1 M)) b0).
             lia. symmetry. eauto. symmetry. eauto.
           }
           {
             move /eqP in Hbm1. move /eqP in Hm1.
             destruct (b_eqb b0 (bid_of m2)) eqn: Hb0m2.
             move /eqP in Hb0m2. subst.
             move /eqP in Hbb0. subst. elim Hbb0. auto. 
             assert(tq m2 > 0). auto.
             assert(tq m1 > 0). auto.
             move /eqP in Hb0m2.
             replace (ttqb M b0) with (ttqb (delete m1 M) b0).
             replace (ttqb (delete m1 M) b0) with 
             (ttqb (delete m2 (delete m1 M)) b0).
             lia. symmetry. eauto. symmetry. eauto.
           }
         }
      } 
    } Qed.



Lemma g_increase_top_ttqa (M:list fill_type)(m1 m2:fill_type)(b:Bid)(a a0:Ask)
(NZT:forall m : fill_type, In m M -> tq m > 0):
In m1 M ->
In m2 M ->
b=bid_of m2 ->
a=ask_of m1 ->
m1<>m2 ->
ttqa (g_increase_top M m2 m1 b a) a0 = ttqa M a0.
Proof.
       destruct (a_eqb a0 a) eqn:Haa0.
       { move /eqP in Haa0. subst. intros.
         eapply g_increase_top_sqa_equal.
         all:auto.
       }
       {
       unfold g_increase_top. intros.  
       destruct (Nat.eqb (tq m2) 1) eqn:Hm1.
       move /eqP in Hm1.
       { destruct (Nat.eqb (tq m1) 1) eqn:Hm2.
         { move /eqP in Hm2.
           simpl. rewrite Haa0.
           destruct (a_eqb a0 (ask_of m2)) eqn: Ha0m2.
           { 
             move /eqP in Ha0m2. replace (ttqa M a0) with 
             (ttqa (delete m1 M) a0).
             replace (ttqa (delete m1 M) a0) with 
             (ttqa (delete m2 (delete m1 M)) a0 + tq m2).
             lia. symmetry. apply ttqa_delete_m_ofa.
             auto.  auto. symmetry. move /eqP in Haa0. 
             subst. eauto.
           }
           {
             move /eqP in Ha0m2. replace (ttqa M a0) with 
             (ttqa (delete m1 M) a0).
             replace (ttqa (delete m1 M) a0) with 
             (ttqa (delete m2 (delete m1 M)) a0).
             lia. symmetry. apply ttqa_delete_m_not_ofa.
             eapply delete_intro with (b0:=m1) in H0.
             auto. auto. auto.
             symmetry. move /eqP in Haa0. 
             subst. eauto.     
           }
         }
         { move /eqP in Hm2.
           simpl. rewrite Haa0.
           destruct (a_eqb a0 (ask_of m2)) eqn: Ha0m2.
           { 
             move /eqP in Ha0m2. 
             destruct (a_eqb a0 (ask_of m1)) eqn:Ha0m1.
             move /eqP in Ha0m1. move /eqP in Haa0. subst.
             auto.
             move /eqP in Ha0m1. move /eqP in Haa0.
             replace (ttqa M a0) with 
             (ttqa (delete m1 M) a0).
             replace (ttqa (delete m1 M) a0) with 
             (ttqa (delete m2 (delete m1 M)) a0 + tq m2).
             assert(tq m1 >0). auto. lia.  
             symmetry. apply ttqa_delete_m_ofa.
             auto. auto. symmetry. eauto.
           }
           {
             move /eqP in Ha0m2. 
             destruct (a_eqb a0 (ask_of m1)) eqn:Ha0m1.
             move /eqP in Ha0m1. move /eqP in Haa0. subst.
             elim Haa0. auto.
             move /eqP in Ha0m1.
             replace (ttqa M a0) with 
             (ttqa (delete m1 M) a0).
             replace (ttqa (delete m1 M) a0) with 
             (ttqa (delete m2 (delete m1 M)) a0).
             lia. symmetry. apply ttqa_delete_m_not_ofa.
             apply delete_intro with (b0:=m1) in H0.
             auto. auto. auto.
             symmetry. eauto.           
           }
         }
       }
       { destruct (Nat.eqb (tq m1) 1) eqn:Hm2.
         { move /eqP in Hm2.
           simpl.  rewrite Haa0.
           destruct (a_eqb a0 (ask_of m2)) eqn: Ha0m2.
           { 
             move /eqP in Ha0m2. move /eqP in Haa0.
             move /eqP in Hm1. 
             assert(tq m2 > 0). auto.
             replace (ttqa M a0) with 
             (ttqa (delete m1 M) a0).
             replace (ttqa (delete m1 M) a0) with 
             (ttqa (delete m2 (delete m1 M)) a0 + tq m2).
             lia. symmetry. eauto. symmetry. subst. eauto.
           }
           {
             move /eqP in Ha0m2. move /eqP in Haa0.
             move /eqP in Hm1. 
             assert(tq m2 > 0). auto. 
             replace (ttqa M a0) with (ttqa (delete m1 M) a0).
             replace (ttqa (delete m1 M) a0) with 
             (ttqa (delete m2 (delete m1 M)) a0).
             lia. symmetry. eauto. symmetry. subst. eauto.
           }
         }
         { move /eqP in Hm2.
           simpl. rewrite Haa0.
           destruct (a_eqb a0 (ask_of m2)) eqn: Ha0m2.
           { 
             move /eqP in Ha0m2. move /eqP in Hm1.
             move /eqP in Haa0.
             destruct (a_eqb a0 (ask_of m1)) eqn: Ha0m1.
             move /eqP in Ha0m1. subst. auto.
             move /eqP in Ha0m1. 
             assert(tq m2 > 0). auto.
             assert(tq m1 > 0). auto.
             replace (ttqa M a0) with (ttqa (delete m1 M) a0).
             replace (ttqa (delete m1 M) a0) with 
             (ttqa (delete m2 (delete m1 M)) a0 + tq m2).
             lia. symmetry. eauto. symmetry. eauto.
           }
           {
             move /eqP in Ha0m2. move /eqP in Hm1.
             move /eqP in Haa0.
             destruct (a_eqb a0 (ask_of m1)) eqn: Ha0m1.
             move /eqP in Ha0m1. subst. 
             elim Haa0. auto. 
             assert(tq m2 > 0). auto.
             assert(tq m1 > 0). auto.
             move /eqP in Ha0m1.
             replace (ttqa M a0) with (ttqa (delete m1 M) a0).
             replace (ttqa (delete m1 M) a0) with 
             (ttqa (delete m2 (delete m1 M)) a0).
             lia. symmetry. eauto. symmetry. eauto.
           }
         }
      } 
    } Qed.


Lemma g_increase_top_ask_notin (M:list fill_type)(m1 m2:fill_type)
(b:Bid)(a a0:Ask):
In m1 M ->
In m2 M ->
b=bid_of m2 ->
a=ask_of m1 ->
~In a0 (asks_of M) -> ~In a0 (asks_of (g_increase_top M m2 m1 b a)).
Proof. intros. assert((asks_of (g_increase_top M m2 m1 b a)) [<=] (asks_of M)). apply g_increase_top_asks_subset. all:auto. Qed.


Lemma g_increase_top_bid_notin (M:list fill_type)(m1 m2:fill_type)
(b b0:Bid)(a:Ask):
In m1 M ->
In m2 M ->
b=bid_of m2 ->
a=ask_of m1 ->
~In b0 (bids_of M) -> ~In b0 (bids_of (g_increase_top M m2 m1 b a)).
Proof. intros. assert((bids_of (g_increase_top M m2 m1 b a)) [<=] (bids_of M)). apply g_increase_top_bids_subset. all:auto. Qed.

Theorem g_increase_top_Is_Uniform (M:list fill_type)(m1 m2:fill_type)
(b:Bid)(a:Ask)(B:list Bid)(A:list Ask)
(NZT:forall m : fill_type, In m M -> tq m > 0):
In m1 M ->
In m2 M ->
b=bid_of m2 ->
a=ask_of m1 ->
m1<>m2 ->
b<> bid_of m1 ->
a<>ask_of m2 ->
Is_uniform M (b::B) (a::A) -> Is_uniform (g_increase_top M m2 m1 b a) (b::B) (a::A).
Proof. intros. split. 
      { apply g_increase_top_Uniform. all:auto. apply H6. }
      split. 
      { split.
            { split.
                { apply g_increase_top_IR_matchable. all:auto;apply H6. }
                { split. intros.
                         assert (ttqb (g_increase_top M m2 m1 b a) b0 = 
                         ttqb M b0).
                         apply g_increase_top_ttqb. all:auto.
                         rewrite H8. assert(In b0 (bids_of M)
                         \/~In b0 (bids_of M)).
                         eauto. destruct H9. apply H6. auto.
                         apply ttqb_elim in H9. lia.
                         intros.
                         assert (ttqa (g_increase_top M m2 m1 b a) a0 = 
                         ttqa M a0).
                         apply g_increase_top_ttqa. all:auto.
                         rewrite H8. assert(In a0 (asks_of M)
                         \/~In a0 (asks_of M)).
                         eauto. destruct H9. apply H6. auto.
                         apply ttqa_elim in H9. lia.
                }
            }
            { split. 
              assert(bids_of (g_increase_top M m2 m1 b a) [<=] bids_of M).
              apply g_increase_top_bids_subset;auto.
              assert(bids_of M [<=](b::B)). apply H6. eauto.
              assert(asks_of (g_increase_top M m2 m1 b a) [<=] asks_of M).
              apply g_increase_top_asks_subset;auto.
              assert(asks_of M [<=](a::A)). apply H6. eauto.
            }
      }
      apply g_increase_top_IR;auto;apply H6.
Qed.

(*#######################End of surgery one#########################*) 


(*########Surgery Two############################*)

Definition increase_quantb_by_one (M:list fill_type)(m:fill_type)(b:Bid)(a:Ask):(list fill_type):=
    if (Nat.eqb (tq m) 1) 
    then (Mk_fill b a 1 (sp a))::(delete m M)
    else 
    (Mk_fill b a 1 (sp a))::
    (Mk_fill (bid_of m) (ask_of m) (tq m - 1)  (tp m))::(delete m M).

Lemma increase_quantb_by_one_size (M:list fill_type)
(m:fill_type)(b:Bid)(a:Ask)
(NZT:(forall m, In m M -> (tq m) > 0)):
In m M ->
QM(M) = QM(increase_quantb_by_one M m b a).
Proof. unfold increase_quantb_by_one. intros. 
       assert(Hdel:forall M m, In m M -> QM(delete m M) =QM(M) - (tq m)).
       intros. eauto.
       assert(QM(M) >= (tq m)). eauto.
       destruct (Nat.eqb (tq m) 1) eqn:Hm.
       { simpl. eapply Hdel in H. move /eqP in Hm. lia. }
       { simpl. eapply Hdel in H as H1. move /eqP in Hm.
         assert(tq m > 0). apply NZT. auto. lia. } Qed.
         
         
Lemma increase_quantb_by_one_NZT (M:list fill_type)(m:fill_type)
(b:Bid)(a:Ask)
(NZT:(forall m, In m M -> (tq m) > 0)):
In m M ->
(forall m0, In m0 (increase_quantb_by_one M m b a) -> (tq m0) > 0).
Proof. unfold increase_quantb_by_one. intros H m0 H0.  
       destruct (Nat.eqb (tq m) 1) eqn:Hm.
       { simpl in H0. destruct H0. subst m0. simpl. lia.
         eauto. }
       { simpl in H0. destruct H0. subst m0. simpl. lia.
         destruct H0. subst m0. simpl. 
         move /eqP in Hm. assert(tq m > 0). 
           apply NZT. auto.  lia. eauto.
       } Qed.

(*Proof that in increase_quantb_by_one, the trade between a and b is increased by single unit.*)

Lemma increase_quantb_by_one_trade_correct (M:list fill_type)(m:fill_type)
(b:Bid)(a:Ask)
(NZT:(forall m, In m M -> (tq m) > 0)):
In m M ->
b=bid_of m ->
a<>ask_of m->
ttq_ab (increase_quantb_by_one M m b a) b a= 1 + ttq_ab M b a.
Proof.
 unfold increase_quantb_by_one. intros.  
       destruct (Nat.eqb (tq m) 1) eqn:Hm. 
       { simpl. replace (a_eqb a a) with true.
         replace (b_eqb b b) with true. simpl.
         replace (ttq_ab M b a) with (ttq_ab (delete m M) b a).
         auto.
         symmetry. eapply ttq_ab_delete. auto. auto.
         eauto. eauto.
       }
       { simpl. replace (a_eqb a a) with true.
         replace (b_eqb b b) with true. simpl. 
         replace (a_eqb a (ask_of m)) with false. 
         replace (b_eqb b (bid_of m)) with true.
         simpl. replace (ttq_ab M b a) with (ttq_ab (delete m M) b a).
         auto. symmetry. eapply ttq_ab_delete.
         auto. auto. destruct (b_eqb b (bid_of m)) eqn: Hbm.
         auto.  move /eqP in Hbm. subst b. elim Hbm. auto. auto.
         eauto. eauto.
} Qed.

(*Proof that trade fill of bid b is invariant in g*)
Lemma increase_quantb_by_one_bqb_equal (M:list fill_type)(m:fill_type)(b:Bid)(a:Ask)
(NZT:(forall m, In m M -> (tq m) > 0)):
In m M ->
b=bid_of m ->
ttqb (increase_quantb_by_one M m b a) b = ttqb M b.
Proof.
 unfold increase_quantb_by_one. intros.  
       destruct (Nat.eqb (tq m) 1) eqn:Hm.
       move /eqP in Hm.
       { simpl. replace (b_eqb b b) with true.  
         replace (ttqb M b) with 
         (ttqb (delete m M) b + tq m). lia.
         symmetry. eauto. eauto.
       }
       { simpl. replace (b_eqb b b) with true.  
         destruct (b_eqb b (bid_of m)) eqn: Hbm.
         { 
           move /eqP in Hbm. 
           assert(tq m > 0). auto. move /eqP in Hm.
           replace (ttqb M b) with (ttqb (delete m M) b + tq m).
           lia. symmetry. eauto.
         }
         { move /eqP in Hbm. subst. elim Hbm. auto. }
         eauto. } Qed. 

(*Proof that quantity ask a is increased by one*)
Lemma increase_quantb_by_one_sqa_by_one (M:list fill_type)(m:fill_type)(b:Bid)(a:Ask)
(NZT:(forall m, In m M -> (tq m) > 0)):
In m M ->
a<>ask_of m ->
ttqa (increase_quantb_by_one M m b a) a = ttqa M a + 1.
Proof.
 unfold increase_quantb_by_one. intros.  
       destruct (Nat.eqb (tq m) 1) eqn:Hm.
 { move /eqP in Hm. simpl.
   replace (a_eqb a a) with true.  
   replace (ttqa M a) with 
   (ttqa (delete m M) a). lia. 
   symmetry. eauto. eauto. 
 }
 { simpl. replace (a_eqb a a) with true.  
   destruct (a_eqb a (ask_of m)) eqn: Ham.
   { move /eqP in Ham. subst. elim H0. auto.
   }
   { move /eqP in Hm. replace (ttqa M a) with 
     (ttqa (delete m M) a). lia. symmetry. eauto.
   } eauto.
 } Qed.
      
      
Lemma increase_quantb_by_one_matching_IR (M:list fill_type)
(m:fill_type)(b:Bid)(a:Ask)
(NZT:(forall m, In m M -> (tq m) > 0)):
In m M ->
Is_IR M ->
b=bid_of m ->
b>=a ->
All_matchable M ->
Is_IR (increase_quantb_by_one M m b a).
Proof. unfold Is_IR. unfold All_matchable.
       unfold increase_quantb_by_one. unfold rational. 
       intros.
       apply H0 in H as Hmp.
       destruct (Nat.eqb (tq m) 1) eqn:Hm.
       { simpl in H4. destruct H4. subst m0. 
         simpl. lia. eauto.
       }
       { simpl in H4. destruct H4. subst m0. simpl. lia. 
           destruct H4. subst m0. simpl. lia. 
           eauto.
       } Qed.

Lemma increase_quantb_by_one_bids_subset (M:list fill_type)
(m:fill_type)(b:Bid)(a:Ask):
In m M ->
b=bid_of m ->
bids_of (increase_quantb_by_one M m b a) [<=] bids_of M.
Proof. unfold increase_quantb_by_one. intros.
       destruct (Nat.eqb (tq m) 1) eqn:Hm.
       { simpl. unfold "[<=]". intros. 
           simpl in H1. 
           destruct H1. subst. eauto. eauto.
       }
       { simpl. unfold "[<=]". intros. 
         simpl in H1. 
         destruct H1. subst. eauto. 
         destruct H1. subst. eauto. 
         eauto.
       } Qed.
       
Lemma increase_quantb_by_one_asks_subset (M:list fill_type)(m:fill_type)(b:Bid)(a:Ask)(A:list Ask):
In m M ->
asks_of M [<=] (a::A) ->
b=bid_of m ->
asks_of (increase_quantb_by_one M m b a) [<=] (a::A).
Proof. unfold increase_quantb_by_one. intros.
       destruct (Nat.eqb (tq m) 1) eqn:Hm.
       { simpl. unfold "[<=]". intros. destruct H2.
         subst a. auto. eauto.
       } 
       { simpl. unfold "[<=]". intros. 
         destruct H2. subst. eauto. 
         destruct H2. subst. eauto. 
         eauto.
       } Qed.



Lemma increase_quantb_by_one_matchable (M:list fill_type)(m:fill_type)(b:Bid)(a:Ask)
(NZT:(forall m, In m M -> (tq m) > 0)):
In m M ->
Is_IR M ->
b=bid_of m ->
b>= a ->
All_matchable M ->
All_matchable (increase_quantb_by_one M m b a).
Proof. intros. assert(Is_IR (increase_quantb_by_one M m b a)). 
       apply increase_quantb_by_one_matching_IR. all:auto. 
       unfold Is_IR in H4. unfold rational in H4.  
       unfold All_matchable. intros.
       apply H4 in H5. lia. Qed.

Lemma increase_quantb_by_one_ttqb (M:list fill_type)(m:fill_type)(b b0:Bid)(a:Ask)
(NZT:forall m : fill_type, In m M -> tq m > 0):
In m M ->
b=bid_of m ->
ttqb (increase_quantb_by_one M m b a) b0 = ttqb M b0.
Proof.
       destruct (b_eqb b0 b) eqn:Hbb0.
       { move /eqP in Hbb0. subst. intros.
         eapply increase_quantb_by_one_bqb_equal.
         all:auto.
       }
       {
       unfold increase_quantb_by_one. intros.  
       destruct (Nat.eqb (tq m) 1) eqn:Hm.
       { simpl. subst. destruct (b_eqb b0 (bid_of m)) eqn: Hbm.
         inversion Hbb0. move /eqP in Hbm. symmetry. eauto.
       }
       { simpl. subst. destruct (b_eqb b0 (bid_of m)) eqn: Hbm.
         inversion Hbb0. move /eqP in Hbm.  symmetry. eauto.
       } } Qed.



Lemma increase_quantb_by_one_ttqa (M:list fill_type)(m:fill_type)(b:Bid)(a a0:Ask)
(NZT:forall m : fill_type, In m M -> tq m > 0):
In m M ->
a0<>a ->
a0<> ask_of m ->
ttqa (increase_quantb_by_one M m b a) a0 = ttqa M a0.
Proof.
       destruct (a_eqb a0 a) eqn:Ha. 
       intros. move /eqP in Ha. subst. elim H0;auto.
       unfold increase_quantb_by_one. intros.  
       destruct (Nat.eqb (tq m) 1) eqn:Hm.
       move /eqP in Hm. simpl. rewrite Ha.
       symmetry; eauto. simpl. rewrite Ha. 
       destruct (a_eqb a0 (ask_of m)) eqn:Ham.
       move /eqP in Ham. subst. elim H1. auto.
       move /eqP in Ham. move /eqP in Hm.
       symmetry;eauto. Qed.



Lemma increase_quantb_by_one_ttqa_ofm (M:list fill_type)(m:fill_type)(b:Bid)(a:Ask)
(NZT:forall m : fill_type, In m M -> tq m > 0):
In m M ->
a<> ask_of m ->
ttqa M (ask_of m)=ttqa (increase_quantb_by_one M m b a) (ask_of m) + 1.
Proof.
       intros. destruct (a_eqb (ask_of m) a) eqn: Ha.
       move /eqP in Ha. subst. elim H0. auto.
       unfold increase_quantb_by_one.  
       destruct (Nat.eqb (tq m) 1) eqn:Hm.
       move /eqP in Hm. simpl.
       rewrite Ha.
       rewrite <- Hm. 
       apply ttqa_delete_m_ofa with (M:=M)(m:=m) (a:=(ask_of m)). all:auto.
       simpl. rewrite Ha. replace (a_eqb (ask_of m) (ask_of m)) with true.
       move /eqP in Hm. 
       cut(ttqa M (ask_of m) = ttqa (delete m M) (ask_of m) + tq m).
       assert(tq m >0). apply NZT. auto.
       lia.  apply ttqa_delete_m_ofa. all:auto. Qed.


Theorem increase_quantb_by_one_matching (M:list fill_type)(m:fill_type)
(b:Bid)(a:Ask)(B:list Bid)(A:list Ask)
(NZT:forall m : fill_type, In m M -> tq m > 0):
In m M ->
b=bid_of m ->
a<>ask_of m ->
b>=a ->
Is_IR M ->
matching_in (b::B) (a::A) M-> 
ttqa M a < sq a ->
matching_in (b::B) (a::A) (increase_quantb_by_one M m b a).
Proof. intros H H0 H1 H2 H3 H4 Hsq. split. 
      { split.
        {  apply increase_quantb_by_one_matchable. all:auto;apply H4. }
        { split. 
          { intros. assert (ttqb (increase_quantb_by_one M m b a) b0 = 
                         ttqb M b0).
                         apply increase_quantb_by_one_ttqb. all:auto.
                         rewrite H6. assert(In b0 (bids_of M)
                         \/~In b0 (bids_of M)).
                         eauto. destruct H7. apply H4. auto.
                         apply ttqb_elim in H7. lia.
          }
          {
          intros. 
          destruct (a_eqb a a0) eqn:Haa0.
          move /eqP in Haa0. subst a0. 
          assert (ttqa (increase_quantb_by_one M m b a) a = 
                         ttqa M a + 1).
          apply increase_quantb_by_one_sqa_by_one. all:auto.
          lia. move /eqP in Haa0.
          destruct (a_eqb a0 (ask_of m)) eqn:Ha0m.
          move /eqP in Ha0m. subst. 
          eapply increase_quantb_by_one_ttqa_ofm with 
          (M:=M)(b:=(bid_of m)) in Haa0. assert(In (ask_of m) (asks_of M)).
          eauto. assert(ttqa M (ask_of m) <= sq (ask_of m)).
          destruct H4. destruct H4. destruct H7. apply H8 in H0.
          lia. lia. all:auto. 
          move /eqP in Ha0m.
          assert(ttqa (increase_quantb_by_one M m b a) a0 = ttqa M a0).
          apply increase_quantb_by_one_ttqa. all:auto.
          rewrite H6. assert(In a0 (asks_of M)
                         \/~In a0 (asks_of M)).
                         eauto. destruct H7. apply H4. auto.
                         apply ttqa_elim in H7. lia.
          
          } } }  
            { split. 
              assert(bids_of (increase_quantb_by_one M m b a) [<=] bids_of M).
              apply increase_quantb_by_one_bids_subset;auto.
              assert(bids_of M [<=](b::B)). apply H4. eauto.
              assert(asks_of (increase_quantb_by_one M m b a) [<=] (a::A)).
              apply increase_quantb_by_one_asks_subset. all:auto.
              apply H4.
            }
Qed.

































(*#######################End of surgery Two########################*)










(************************************************************************)

(*########Surgeries for the existence of M'  = M - q matchings ############*)

(*This function removes trades for a given pair of bid and ask. 
This is used in the proofs maximality for MM and UM. We claim that
given a matching M there exists another matching M' in the reduced list of
Bids and Asks such that the size of M' is equal to size of M minus q, 
where q is quanity traded between the a pair of bid and ask.*)



(**************** case when the bid and ask are fully traded **********************)


Fixpoint Remove_ab_trades (M:list fill_type)(b:Bid)(a:Ask) :=
match M with 
| nil => nil
| m::M' => match ((a_eqb a (ask_of m)) && (b_eqb b (bid_of m))) with 
      |true => Remove_ab_trades M' b a
      |false => m::(Remove_ab_trades M' b a)
    end
end.

Lemma Remove_ab_trades_elim1 (M:list fill_type)(b:Bid)(a:Ask)(m:fill_type):
In m (Remove_ab_trades M b a) -> In m M.
Proof. induction M as [|m' M']. simpl. auto.
simpl. destruct (a_eqb a (ask_of m') && b_eqb b (bid_of m')) eqn:H.
intros. right. apply IHM'. auto. simpl. intros.
destruct H0. auto. auto. Qed.

Lemma Remove_ab_trades_intro1 (M:list fill_type)(b:Bid)(a:Ask)(m:fill_type):
~In m M -> ~In m (Remove_ab_trades M b a).
Proof. induction M as [|m' M']. simpl. auto.
simpl. destruct (a_eqb a (ask_of m') && b_eqb b (bid_of m')) eqn:H.
intros. apply IHM'. eauto. intros.
simpl. intro. destruct H1. subst m. eauto.
assert(~ In m (Remove_ab_trades M' b a)).
apply IHM'. eauto. auto. Qed.


Lemma Remove_ab_trades_correct1 (M:list fill_type)(b:Bid)(a:Ask) :
ttq_ab (Remove_ab_trades M b a) b a =0.
Proof. induction M as [|m M']. simpl. auto.
simpl. destruct (a_eqb a (ask_of m) && b_eqb b (bid_of m)) eqn:H.
apply IHM'. simpl. rewrite H. apply IHM'. Qed.

Lemma Remove_ab_trades_correct2a (M:list fill_type)(b:Bid)(a:Ask) :
ttqa M a = ttq_ab M b a + ttqa (Remove_ab_trades M b a) a.
Proof. induction M as [|m M']. simpl. auto.
simpl. destruct (a_eqb a (ask_of m) && b_eqb b (bid_of m)) eqn:Hab.
{
  destruct (a_eqb a (ask_of m)) eqn: Ha;destruct (b_eqb b (bid_of m)) eqn: Hb.
  { rewrite IHM'. lia. } 
  { simpl in Hab. auto. }
  { simpl in Hab. auto. }
  { simpl in Hab. auto. }
}
{
  destruct (a_eqb a (ask_of m)) eqn: Ha;destruct (b_eqb b (bid_of m)) eqn: Hb.
  { simpl in Hab. symmetry in Hab. auto. }
  { simpl. rewrite Ha. rewrite IHM'.  lia. } 
  {  simpl. rewrite Ha. rewrite IHM'.  lia. }
  {  simpl. rewrite Ha. rewrite IHM'.  lia. }
} Qed.

Lemma Remove_ab_trades_correct2b (M:list fill_type)(b:Bid)(a:Ask) :
ttqb M b = ttq_ab M b a + ttqb (Remove_ab_trades M b a) b.
Proof. induction M as [|m M']. simpl. auto.
simpl. destruct (a_eqb a (ask_of m) && b_eqb b (bid_of m)) eqn:Hab.
{
  destruct (a_eqb a (ask_of m)) eqn: Ha;destruct (b_eqb b (bid_of m)) eqn: Hb.
  { rewrite IHM'. lia. } 
  { simpl in Hab. auto. }
  { simpl in Hab. auto. }
  { simpl in Hab. auto. }
}
{
  destruct (a_eqb a (ask_of m)) eqn: Ha;destruct (b_eqb b (bid_of m)) eqn: Hb.
  { simpl in Hab. symmetry in Hab. auto. }
  { simpl. rewrite Hb. rewrite IHM'.  lia. } 
  {  simpl. rewrite Hb. rewrite IHM'.  lia. }
  {  simpl. rewrite Hb. rewrite IHM'.  lia. }
} Qed.

Lemma Remove_ab_trades_NZT (M:list fill_type)(b:Bid)(a:Ask) 
(NZT: forall m : fill_type, In m M -> tq m > 0):
forall m : fill_type, In m (Remove_ab_trades M b a) -> tq m > 0.
Proof. intros. assert(In m M \/ ~In m M). eauto.
destruct H0. apply NZT in H0. auto. 
apply Remove_ab_trades_intro1 with (b:=b)(a:=a) in H0. 
unfold not in H0. apply H0 in H. elim H. Qed.

Lemma Remove_ab_trades_matchable (M:list fill_type)(b:Bid)(a:Ask) :
All_matchable M -> All_matchable (Remove_ab_trades M b a).
Proof. induction M as [|m M']. simpl. auto.
simpl. destruct (a_eqb a (ask_of m) && b_eqb b (bid_of m)) eqn:Hab.
{
  unfold All_matchable. simpl. intros H m' Hm'.
  specialize (H m') as Hm1'. destruct Hm1'. right. 
  eapply Remove_ab_trades_elim1. eauto.
  unfold All_matchable in IHM'. eapply IHM' in Hm'.
  auto. intros. apply H. right. auto. lia.
} 
{
  unfold All_matchable. simpl. intros H m' Hm'. destruct Hm'.
  apply H. auto. apply H. right. eapply Remove_ab_trades_elim1.
  eauto.
} Qed.

Lemma Remove_ab_trades_ttq_le_a (M:list fill_type)(b:Bid)(a a0:Ask):
ttqa (Remove_ab_trades M b a) a0 <= ttqa M a0.
Proof. induction M as [|m M']. simpl. auto.
simpl. destruct ((a_eqb a (ask_of m)) && (b_eqb b (bid_of m))) eqn:Hab.
{ destruct ((a_eqb a0 (ask_of m))) eqn: Ha0. 
  {
    destruct (a_eqb a a0) eqn:Haa0.
    { move /eqP in Haa0. subst a0. 
      assert(ttqa M' a = ttq_ab M' b a + ttqa (Remove_ab_trades M' b a) a).
      eapply Remove_ab_trades_correct2a.
      rewrite H. lia.
    }
    { move /eqP in Haa0. 
      destruct(a_eqb a (ask_of m)) eqn: Hf.
      move /eqP in Ha0.
      move /eqP in Hf.
      subst a. subst a0. elim Haa0. auto.
      simpl in Hab. inversion Hab.
     }
   }
   {
   apply IHM'.
   }
 }
 { destruct ((a_eqb a0 (ask_of m))) eqn: Ha0. 
  {
    simpl. rewrite Ha0. lia. 
  }
  { simpl. rewrite Ha0. lia.
  }
 } Qed.


Lemma Remove_ab_trades_ttq_le_b (M:list fill_type)(b b0:Bid)(a:Ask):
ttqb (Remove_ab_trades M b a) b0 <= ttqb M b0.
Proof. induction M as [|m M']. simpl. auto.
simpl. destruct ((a_eqb a (ask_of m)) && (b_eqb b (bid_of m))) eqn:Hab.
{ destruct ((b_eqb b0 (bid_of m))) eqn: Hb0. 
  {
    destruct (b_eqb b b0) eqn:Hbb0.
    { move /eqP in Hbb0. subst b0. 
      assert(ttqb M' b = ttq_ab M' b a + ttqb (Remove_ab_trades M' b a) b).
      eapply Remove_ab_trades_correct2b.
      rewrite H. lia.
    }
    { move /eqP in Hbb0. 
      destruct(b_eqb b (bid_of m)) eqn: Hf.
      move /eqP in Hb0.
      move /eqP in Hf.
      subst b. subst b0. elim Hbb0. auto.
      destruct (a_eqb a (ask_of m)).
      simpl in Hab. inversion Hab.
      simpl in Hab. inversion Hab.
     }
   }
   {
   apply IHM'.
   }
 }
 { destruct ((b_eqb b0 (bid_of m))) eqn: Hb0. 
  {
    simpl. rewrite Hb0. lia. 
  }
  { simpl. rewrite Hb0. lia.
  }
 } Qed.

Lemma Remove_ab_trades_b_notIn (M:list fill_type)(b:Bid)(a:Ask)
(NZT: forall m : fill_type, In m M -> tq m > 0):
ttqb M b <= bq b -> ttq_ab M b a = bq b -> ~In b (bids_of (Remove_ab_trades M b a)).
Proof. intros. assert(ttqb M b = ttq_ab M b a + ttqb (Remove_ab_trades M b a) b). apply Remove_ab_trades_correct2b.
assert (ttqb (Remove_ab_trades M b a) b = 0). lia.
apply ttqb_intro in H2. auto. 
apply Remove_ab_trades_NZT. auto. Qed.

Lemma Remove_ab_trades_a_notIn (M:list fill_type)(b:Bid)(a:Ask)
(NZT: forall m : fill_type, In m M -> tq m > 0):
ttqa M a <= sq a -> ttq_ab M b a = sq a -> ~In a (asks_of (Remove_ab_trades M b a)).
Proof. intros. assert(ttqa M a = ttq_ab M b a + ttqa (Remove_ab_trades M b a) a). apply Remove_ab_trades_correct2a.
assert (ttqa (Remove_ab_trades M b a) a = 0). lia.
apply ttqa_intro in H2. auto. 
apply Remove_ab_trades_NZT. auto. Qed.


Lemma Remove_ab_trades_bids_subset (M:list fill_type)(b:Bid)(a:Ask):
bids_of (Remove_ab_trades M b a) [<=] bids_of M.
Proof. induction M as [|m M']. simpl. auto.
simpl. destruct ((a_eqb a (ask_of m)) && (b_eqb b (bid_of m))) eqn:Hab.
eauto. simpl. eapply Subset_intro. auto. Qed.

Lemma Remove_ab_trades_asks_subset (M:list fill_type)(b:Bid)(a:Ask):
asks_of (Remove_ab_trades M b a) [<=] asks_of M.
Proof. induction M as [|m M']. simpl. auto.
simpl. destruct ((a_eqb a (ask_of m)) && (b_eqb b (bid_of m))) eqn:Hab.
eauto. simpl. eapply Subset_intro. auto. Qed.

Lemma Remove_ab_trades_QM (M:list fill_type)(b:Bid)(a:Ask):
QM (M) = QM (Remove_ab_trades M b a) + ttq_ab M b a.
Proof. induction M as [|m M']. simpl. auto.
simpl. destruct ((a_eqb a (ask_of m)) && (b_eqb b (bid_of m))) eqn:Hab.
simpl. lia. simpl. lia. Qed.

Lemma Remove_ab_trades_IR (M:list fill_type)(b:Bid)(a:Ask):
Is_IR M-> Is_IR (Remove_ab_trades M b a).
Proof. unfold Is_IR. intros. assert(In m M \/ ~In m M).
eauto. destruct H1. auto. 
apply Remove_ab_trades_intro1 with (b:=b)(a:=a) in H1.
unfold not in H1. apply H1 in H0. elim H0.

Qed.

Lemma Remove_ab_trades_Uniform (M:list fill_type)(b:Bid)(a:Ask):
Uniform M-> Uniform (Remove_ab_trades M b a).
Proof. induction M as [|m M'].
simpl. auto. unfold Uniform. simpl. 
intros. destruct ((a_eqb a (ask_of m)) && (b_eqb b (bid_of m))) eqn:Hab.
simpl in H. apply IHM'. unfold Uniform. 
apply uniform_elim2 with (a0:=tp m) in H. auto.
simpl. unfold Uniform in IHM'.
apply uniform_elim2 with (a0:=tp m) in H as H1.
apply IHM' in H1 as H2. 
cut((forall x, In x (trade_prices_of (Remove_ab_trades M' b a)) -> x=tp m)).
eapply uniform_intro. intros.
assert(In x (trade_prices_of M')).
assert(exists m0, (In m0 (Remove_ab_trades M' b a) /\ (x = tp m0))).
eauto.
destruct H3 as [m0 H3]. destruct H3.
assert(In m0 M').
eapply Remove_ab_trades_elim1 with(b:=b)(a:=a). auto.
subst x.
eauto.
assert(forall x, In x (trade_prices_of M') -> x=tp m).
eapply uniform_elim. auto. apply H4 in H3. 
auto.
Qed.

Lemma exists_M0_reduced_bid_ask_matching (M:list fill_type) (B:list Bid)(A:list Ask)(b:Bid)(a:Ask)
(NZT:forall m : fill_type, In m M -> tq m > 0):
matching_in (b::B) (a::A) M-> 
ttq_ab M b a = (bq b) /\ ((sq a) = (bq b)) ->
Is_IR M ->
(exists M0, (matching_in B A M0) /\Is_IR M0/\(QM(M)=QM(M0) + (bq b))/\
(forall m : fill_type, In m M0 -> tq m > 0)).
Proof. intros H H0 IR. exists (Remove_ab_trades M b a).
split. 
  { split.
    split. 
    { apply Remove_ab_trades_matchable. apply H. }
      split.
      { intros. 
        assert(ttqb (Remove_ab_trades M b a) b0 <= ttqb M b0). 
        eapply Remove_ab_trades_ttq_le_b with (b0:=b0).
        assert(ttqb M b0 <= bq b0).  
        assert(In b0 (bids_of M) \/~In b0 (bids_of M)).
        eauto. destruct H3. 
        apply H. auto. apply ttqb_elim in H3. lia. lia.
      }
      { intros. 
        assert(ttqa (Remove_ab_trades M b a) a0 <= ttqa M a0). 
        eapply Remove_ab_trades_ttq_le_a with (a0:=a0).
        assert(ttqa M a0 <= sq a0).
        assert(In a0 (asks_of M) \/~In a0 (asks_of M)).
        eauto. destruct H3. 
        apply H. auto. apply ttqa_elim in H3. lia. lia.
      }
      { split. 
        { assert(bids_of (Remove_ab_trades M b a) [<=] bids_of M).
          apply Remove_ab_trades_bids_subset.
          assert(bids_of M [<=] (b::B)).
          apply H.
          assert(bids_of (Remove_ab_trades M b a) [<=] (b::B)).
          eauto. 
          assert(~In b (bids_of (Remove_ab_trades M b a))).
          apply Remove_ab_trades_b_notIn.
          auto. assert(In b (bids_of M) \/~In b (bids_of M)).
          eauto. destruct H4. 
          apply H. auto. apply ttqb_elim in H4. lia. 
          apply H0. eauto.
        }
        { assert(asks_of (Remove_ab_trades M b a) [<=] asks_of M).
          apply Remove_ab_trades_asks_subset.
          assert(asks_of M [<=] (a::A)).
          apply H.
          assert(asks_of (Remove_ab_trades M b a) [<=] (a::A)).
          eauto. 
          assert(~In a (asks_of (Remove_ab_trades M b a))).
          apply Remove_ab_trades_a_notIn.
          auto. assert(In a (asks_of M) \/~In a (asks_of M)).
          eauto. destruct H4. 
          apply H. auto. apply ttqa_elim in H4. lia. 
          destruct H0. lia. eauto.
        }
    }
  }
  { split.
  apply Remove_ab_trades_IR. apply IR.
  destruct H0. rewrite<- H0. split.
  apply Remove_ab_trades_QM. 
   apply Remove_ab_trades_NZT. auto.
 } Qed.




Theorem exists_M0_reduced_bid_ask_uniform (M:list fill_type) (B:list Bid)(A:list Ask)(b:Bid)(a:Ask)
(NZT:forall m : fill_type, In m M -> tq m > 0):
Is_uniform M (b::B) (a::A) -> ttq_ab M b a = (bq b) /\ ((sq a) = (bq b)) ->
(exists M0, (Is_uniform M0 B A) /\(QM(M)=QM(M0) + (bq b))/\
(forall m : fill_type, In m M0 -> tq m > 0)).
Proof. intros. exists (Remove_ab_trades M b a).
split. 
{ split.
  { apply Remove_ab_trades_Uniform. apply H. }
  split. 
  { split. 
    { split. apply Remove_ab_trades_matchable. apply H.
      split.
      { intros. 
        assert(ttqb (Remove_ab_trades M b a) b0 <= ttqb M b0). 
        eapply Remove_ab_trades_ttq_le_b with (b0:=b0).
        assert(ttqb M b0 <= bq b0).  assert(In b0 (bids_of M) \/~In b0 (bids_of M)).
        eauto. destruct H3. 
        apply H. auto. apply ttqb_elim in H3. lia. lia.
      }
      { intros. 
        assert(ttqa (Remove_ab_trades M b a) a0 <= ttqa M a0). 
        eapply Remove_ab_trades_ttq_le_a with (a0:=a0).
        assert(ttqa M a0 <= sq a0).  assert(In a0 (asks_of M) \/~In a0 (asks_of M)).
        eauto. destruct H3. 
        apply H. auto. apply ttqa_elim in H3. lia. lia.
      }
    }
    { split. 
      { assert(bids_of (Remove_ab_trades M b a) [<=] bids_of M).
        apply Remove_ab_trades_bids_subset.
        assert(bids_of M [<=] (b::B)).
        apply H.
        assert(bids_of (Remove_ab_trades M b a) [<=] (b::B)).
        eauto. 
        assert(~In b (bids_of (Remove_ab_trades M b a))).
        apply Remove_ab_trades_b_notIn.
        auto. assert(In b (bids_of M) \/~In b (bids_of M)).
        eauto. destruct H4. 
        apply H. auto. apply ttqb_elim in H4. lia. 
        apply H0. eauto.
      }
      { assert(asks_of (Remove_ab_trades M b a) [<=] asks_of M).
        apply Remove_ab_trades_asks_subset.
        assert(asks_of M [<=] (a::A)).
        apply H.
        assert(asks_of (Remove_ab_trades M b a) [<=] (a::A)).
        eauto. 
        assert(~In a (asks_of (Remove_ab_trades M b a))).
        apply Remove_ab_trades_a_notIn.
        auto. assert(In a (asks_of M) \/~In a (asks_of M)).
        eauto. destruct H4. 
        apply H. auto. apply ttqa_elim in H4. lia. 
        destruct H0. lia. eauto.
      }
    }
  }
  {
  apply Remove_ab_trades_IR. apply H.
  }
 }
 split.
 { destruct H0. rewrite<- H0.
  apply Remove_ab_trades_QM.
 }
 {
 apply Remove_ab_trades_NZT. auto.
 } Qed.

(**************** case when the bid is partially traded *****************************)

Fixpoint replace_bid (M:list fill_type)(b b':Bid):=
match M with 
|nil => nil
|m::M' =>match (b_eqb b (bid_of m)) with
  |true => (Mk_fill b' (ask_of m) (tq m) (tp m))::replace_bid M' b b'
  |false =>m::replace_bid M' b b'
  end
end.

Lemma replace_bid_elim1 (M:list fill_type)(b b':Bid) :
b=b' -> M = replace_bid M b b'.
Proof.  intros. induction M as [|m' M']. simpl. auto.
simpl. destruct (b_eqb b (bid_of m')) eqn: Hbm'.
simpl. f_equal. subst b'. move /eqP in Hbm'.
subst b. destruct m'. auto. auto. f_equal. auto. Qed.

Lemma replace_bid_elim2 (M:list fill_type)(b b':Bid) :
b<>b' -> ~In b (bids_of (replace_bid M b b')).
Proof.  intros. induction M as [|m' M']. simpl. auto.
simpl. destruct (b_eqb b (bid_of m')) eqn: Hbm'.
simpl. eauto. simpl. intro. destruct H0. move /eqP in Hbm'.
subst b. elim Hbm'. auto. eauto. Qed.


Lemma replace_bid_subset_ask (M:list fill_type)(b b':Bid):
asks_of M = asks_of (replace_bid M b b').
Proof.
revert b b'. induction M as [|m' M']. simpl. auto.
intros. simpl. destruct (b_eqb b (bid_of m')) eqn: Hbm'.
simpl. f_equal. apply IHM'.
simpl. f_equal. apply IHM'. Qed.

Lemma replace_bid_subset_prices (M:list fill_type)(b b':Bid):
trade_prices_of M = trade_prices_of (replace_bid M b b').
Proof.
revert b b'. induction M as [|m' M']. simpl. auto.
intros. simpl. destruct (b_eqb b (bid_of m')) eqn: Hbm'.
simpl. f_equal. apply IHM'.
simpl. f_equal. apply IHM'. Qed.

Lemma replace_bid_subset_bids (M:list fill_type)(b b':Bid)(B:list Bid):
bids_of M [<=] (b::B) -> bids_of (replace_bid M b b') [<=] (b'::B).
Proof.
revert b b' B. induction M as [|m' M']. simpl. auto.
intros. simpl. destruct (b_eqb b (bid_of m')) eqn: Hbm'.
simpl. simpl in H. assert(bids_of M' [<=] b :: B). 
eauto.  eapply IHM' with(b:=b)(b':=b') in H0.
unfold Subset. intros. destruct H1.
simpl. auto. eauto. simpl. simpl in H.
eapply Subset_elim1 in H as H1.
destruct H1. move /eqP in Hbm'. subst b.
elim Hbm'. auto.
eapply Subset_elim2 in H. eapply IHM' with (b:=b)(b':=b') in H.
unfold Subset.
intros. simpl. destruct H1. right. subst a. auto.
unfold Subset in H. apply H in H1.
destruct H1. left. auto. auto. Qed.

Lemma replace_bid_matchable (M:list fill_type)(b b':Bid):
All_matchable M -> Nat.eqb (bp b) (bp b')-> All_matchable (replace_bid M b b').
Proof. induction M as [|m M']. simpl. auto.
unfold All_matchable.  
simpl. intros. 
destruct (b_eqb b (bid_of m)) eqn: Hm. 
{
  move /eqP in Hm. subst b.
  destruct H1. 
  { subst m0. simpl.
    specialize (H m). 
    destruct H. auto. move /eqP in H0. lia.
    move /eqP in H0. lia. 
  }
  eapply IHM' in H0.
  unfold All_matchable in H0. apply H0 in H1. auto.
  unfold All_matchable. intros. 
  specialize (H m1) as H3. 
  destruct H3. right. auto. auto. lia.
}
{
simpl in H1. destruct H1.
move /eqP in Hm. subst m. auto.
eapply IHM' in H0.  
apply H0 in H1. auto. 
unfold All_matchable. intros.
specialize (H m1) as H3.
destruct H3. auto. auto. lia.
} Qed. 


Lemma replace_bid_ttqb_b_b' (M:list fill_type)(b b':Bid):
~In b' (bids_of M) -> ttqb M b =ttqb (replace_bid M b b') b'.
Proof. induction M as [|m M']. simpl. auto.
simpl. 
destruct (b_eqb b (bid_of m)) eqn: Hm. 
{ simpl. destruct (b_eqb b' b') eqn:Hbb'.
  intros. assert(~ In b' (bids_of M')).
  unfold not in H. auto. apply IHM' in H0. lia.
  move /eqP in Hbb'. elim Hbb'. auto.
}
{ simpl. destruct (b_eqb b' (bid_of m)) eqn:Hbm.
  intros. unfold not in H. 
  move /eqP in Hbm. symmetry in Hbm. 
  destruct H. auto. 
  intros. apply IHM'. auto.
}
Qed. 



Lemma replace_bid_ttqb_b0 (M:list fill_type)(b b' b0:Bid):
b0<>b'/\b0<>b -> ttqb M b0 = ttqb (replace_bid M b b') b0.
Proof. induction M as [|m M']. simpl. auto.
simpl. 
destruct (b_eqb b0 (bid_of m)) eqn: Hm. 
{ simpl. destruct (b_eqb b (bid_of m)) eqn:Hbm.
  intros. destruct H. 
  move /eqP in Hbm. move /eqP in Hm. 
  subst. elim H0. auto. 
  intros. destruct H. simpl.
  rewrite Hm. rewrite IHM'.
  auto. lia. 
}
{ destruct (b_eqb b (bid_of m)) eqn:Hbm.
  intros. simpl. destruct H. 
  destruct (b_eqb b0 b') eqn:Hb.
  move /eqP in Hb. subst. elim H. auto. 
  apply IHM'. auto. simpl.
  rewrite Hm. auto. 
}
Qed.
 
Lemma replace_bid_ttqa (M:list fill_type)(a:Ask)(b b':Bid):
ttqa M a = ttqa (replace_bid M b b') a.
Proof. induction M as [|m M']. simpl. auto.
simpl. 
destruct (a_eqb a (ask_of m)) eqn: Hm. 
{ destruct (b_eqb b (bid_of m)) eqn:Hbm.
  simpl. rewrite Hm. lia. 
  simpl.
  rewrite Hm. lia.
}
{ destruct (b_eqb b (bid_of m)) eqn:Hbm.
  simpl. rewrite Hm. lia. 
  simpl.
  rewrite Hm. lia.
}
Qed.

Lemma replace_bid_Uniform (M:list fill_type)(b b':Bid):
Uniform M -> Uniform (replace_bid M b b').
Proof. unfold Uniform. 
assert(trade_prices_of M = trade_prices_of (replace_bid M b b')).
eapply replace_bid_subset_prices.
rewrite H. auto. Qed.


Lemma replace_bid_IR (M:list fill_type)(b b':Bid):
Is_IR M -> b' >= b -> Is_IR (replace_bid M b b').
Proof. induction M as [|m M']. simpl. auto.
unfold Is_IR.  
simpl. intros. 
destruct (b_eqb b (bid_of m)) eqn: Hm. 
{
  move /eqP in Hm. subst b.
  destruct H1. 
  { subst m0. unfold rational.
    simpl.
    specialize (H m). 
    destruct H. auto. 
    lia.
  }
  eapply IHM' in H0.
  unfold Is_IR in H0. apply H0 in H1. auto.
  unfold Is_IR. intros. 
  specialize (H m1) as H3. 
  destruct H3. right. auto. auto.
}
{
simpl in H1. destruct H1.
move /eqP in Hm. subst m. auto.
eapply IHM' in H0.  
apply H0 in H1. auto. 
unfold Is_IR. intros.
specialize (H m1) as H3.
destruct H3. auto. auto. 
} Qed. 

Lemma replace_bid_QM (M:list fill_type)(b b':Bid):
QM(M) = QM(replace_bid M b b').
Proof. induction M as [|m M']. simpl. auto.
simpl. destruct (b_eqb b (bid_of m)) eqn: Hm. simpl. lia.
simpl. lia. Qed.

Lemma replace_bid_NZT (M:list fill_type)(b b':Bid)
(NZT:forall m : fill_type, In m M -> tq m > 0):
(forall m : fill_type, In m (replace_bid M b b') -> tq m > 0).
Proof. induction M as [|m M']. simpl. auto.
simpl. destruct (b_eqb b (bid_of m)) eqn: Hm. simpl.
intros. destruct H. subst m0. simpl. eauto.
apply IHM'. eauto. auto. 
simpl. intros. destruct H. subst m0.
apply NZT. eauto. apply IHM'.
eauto. auto. Qed.

Lemma replace_bid_matching1 (M:list fill_type)(B:list Bid)(A:list Ask)(b b':Bid)
(NDB:NoDup (b'::B)):
matching_in (b::B) A M-> ttqb M b <= bq b' -> Nat.eqb (bp b) (bp b') ->
matching_in (b'::B) A (replace_bid M b b').
Proof. intros.  split.
{ split. 
  { apply replace_bid_matchable. apply H. auto. }
  { split. 
    { intros. destruct (b_eqb b b') eqn:Hbb'.
      { move /eqP in Hbb'. apply replace_bid_elim1 with (M:=M) in Hbb'.
        rewrite <- Hbb'. assert(In b0 (bids_of M)\/~In b0 (bids_of M)).
        eauto. destruct H3. apply H. auto.
        apply ttqb_elim in H3. lia.
      }
      { destruct (b_eqb b0 b') eqn:Hb0b';destruct (b_eqb b0 b) eqn:Hb0b.
        {
          move /eqP in Hb0b'. move /eqP in Hb0b.
          move /eqP in Hbb'. subst. elim Hbb'. auto.
        }
        {
          move /eqP in Hbb'. apply replace_bid_elim2 with (M:=M) in Hbb'.
          move /eqP in Hb0b'. subst. replace (ttqb (replace_bid M b b') b')
          with (ttqb M b). auto. apply replace_bid_ttqb_b_b'.
          assert((bids_of M)[<=](b::B)). apply H. intro.
          assert(In b' (b :: B)). eauto. destruct H5. 
          move /eqP in Hb0b. subst. elim Hb0b. auto.
          apply nodup_elim2 in NDB. eauto.
        }
        {
          move /eqP in Hbb'. apply replace_bid_elim2 with (M:=M) in Hbb'.
          move /eqP in Hb0b. subst. unfold not in Hbb'. 
          apply Hbb' in H2. elim H2.
        }
        {
          move /eqP in Hb0b'. move /eqP in Hb0b.
          move /eqP in Hbb'. replace (ttqb (replace_bid M b b') b0) 
          with (ttqb M b0). assert(In b0 (bids_of M)\/~In b0 (bids_of M)).
          eauto. destruct H3. apply H. auto.
          apply ttqb_elim in H3. lia.
          eapply replace_bid_ttqb_b0. auto.
         }
       }
    }
    {
    intros. replace (ttqa (replace_bid M b b') a) with (ttqa M a).
    assert(In a (asks_of M)\/~In a (asks_of M)).
    eauto. destruct H3. apply H. auto.
    apply ttqa_elim in H3. lia. apply replace_bid_ttqa.
    }
  }
}
{
  split.
  { apply replace_bid_subset_bids. apply H. }
  { rewrite <- replace_bid_subset_ask. apply H. }
} Qed.

Lemma exists_M0_reduced_bid_uniform (M:list fill_type)(B:list Bid)(A:list Ask)(b:Bid)(a:Ask)
(NDB:NoDup (idbs_of (b::B)))
(NZT:forall m : fill_type, In m M -> tq m > 0):
Is_uniform M (b::B) (a::A) -> 
ttq_ab M b a = (sq a) ->
((bq b) > (sq a)) -> 
exists M0, (Is_uniform M0 ((Mk_bid (bp b) (btime b) (bq b - (sq a)) (idb b))::B)
A)
/\(QM(M)=QM(M0) + (sq a)/\
(forall m : fill_type, In m M0 -> tq m > 0)).
Proof. intros. 
set (b':={| bp := b; btime := btime b; bq := bq b - sq a; idb := idb b |}).
exists (replace_bid (Remove_ab_trades M b a) b b').
split. 
  { split.
    { apply replace_bid_Uniform. apply Remove_ab_trades_Uniform. apply H. }
    split. 
    { apply replace_bid_matching1. apply idbs_of_nodup. simpl.
      simpl in NDB. auto.
      { split. (*Proof that matching *)
        split.
        apply Remove_ab_trades_matchable. apply H.
        split. 
        { intros. assert(ttqb (Remove_ab_trades M b a) b0 <= ttqb M b0).
          apply Remove_ab_trades_ttq_le_b.
          assert(ttqb M b0 <= bq b0). 
          assert(In b0 (bids_of M)\/~In b0 (bids_of M)).
          eauto. destruct H4. apply H. auto.
          apply ttqb_elim in H4. lia. lia.
        }
        { intros. assert(ttqa (Remove_ab_trades M b a) a0 <= ttqa M a0).
          apply Remove_ab_trades_ttq_le_a.
          assert(ttqa M a0 <= sq a0). 
          assert(In a0 (asks_of M)\/~In a0 (asks_of M)).
          eauto. destruct H4. apply H. auto.
          apply ttqa_elim in H4. lia. lia.
        }
        split. assert(bids_of (Remove_ab_trades M b a) [<=] bids_of M).
        apply Remove_ab_trades_bids_subset.
        assert(bids_of M [<=] (b::B)). apply H.
        eauto.
        assert(asks_of (Remove_ab_trades M b a) [<=] asks_of M).
        apply Remove_ab_trades_asks_subset.
        assert(asks_of M [<=] (a::A)).  apply H.
        assert(~In a (asks_of (Remove_ab_trades M b a))).
        apply Remove_ab_trades_a_notIn. auto. 
        assert(In a (asks_of M)\/~In a (asks_of M)).
        eauto. destruct H4. apply H. auto.
        apply ttqa_elim in H4. lia. lia.
        assert(asks_of (Remove_ab_trades M b a) [<=] (a::A)).
        eauto. eauto.
      }        
      subst b'. 
      simpl. assert (ttqb M b = (ttq_ab M b a) + (ttqb (Remove_ab_trades M b a) b)).
      apply Remove_ab_trades_correct2b. 
      assert(In b (bids_of M)\/~In b (bids_of M)).
      eauto. destruct H3.
      assert(ttqb M b <= bq b). apply H. auto. lia.
       apply ttqb_elim in H3. lia. subst b'. simpl. auto. 
    }
    { apply replace_bid_IR. apply Remove_ab_trades_IR. apply H.
      subst b'. simpl. auto.
    }
  }
  split.
{ 
  replace (QM (replace_bid (Remove_ab_trades M b a) b b')) with 
  (QM (Remove_ab_trades M b a)). 
  assert(QM M = QM (Remove_ab_trades M b a) + ttq_ab M b a). 
  apply Remove_ab_trades_QM. lia.
  apply replace_bid_QM.
}
{
apply replace_bid_NZT.
apply Remove_ab_trades_NZT.
auto.
} Qed.
   

Lemma exists_M0_reduced_bid_matching (M:list fill_type)(B:list Bid)(A:list Ask)(b:Bid)(a:Ask)
(NDB:NoDup (idbs_of (b::B)))
(NZT:forall m : fill_type, In m M -> tq m > 0):
matching_in (b::B) (a::A) M-> 
ttq_ab M b a = (sq a) ->
((bq b) > (sq a)) -> 
Is_IR M ->
exists M0, (matching_in ((Mk_bid (bp b) (btime b) (bq b - (sq a)) (idb b))::B)
A M0)
/\(QM(M)=QM(M0) + (sq a)/\Is_IR M0 /\
(forall m : fill_type, In m M0 -> tq m > 0)).
Proof. intros. 
set (b':={| bp := b; btime := btime b; bq := bq b - sq a; idb := idb b |}).
exists (replace_bid (Remove_ab_trades M b a) b b').
split. { apply replace_bid_matching1. apply idbs_of_nodup. simpl.
      simpl in NDB. auto.
      { split. (*Proof that matching *)
        split.
        apply Remove_ab_trades_matchable. apply H.
        split. 
        { intros. assert(ttqb (Remove_ab_trades M b a) b0 <= ttqb M b0).
          apply Remove_ab_trades_ttq_le_b.
          assert(ttqb M b0 <= bq b0). 
          assert(In b0 (bids_of M)\/~In b0 (bids_of M)).
          eauto. destruct H5. apply H. auto.
          apply ttqb_elim in H5. lia. lia.
        }
        { intros. assert(ttqa (Remove_ab_trades M b a) a0 <= ttqa M a0).
          apply Remove_ab_trades_ttq_le_a.
          assert(ttqa M a0 <= sq a0). 
          assert(In a0 (asks_of M)\/~In a0 (asks_of M)).
          eauto. destruct H5. apply H. auto.
          apply ttqa_elim in H5. lia. lia.
        }
        split. assert(bids_of (Remove_ab_trades M b a) [<=] bids_of M).
        apply Remove_ab_trades_bids_subset.
        assert(bids_of M [<=] (b::B)). apply H.
        eauto.
        assert(asks_of (Remove_ab_trades M b a) [<=] asks_of M).
        apply Remove_ab_trades_asks_subset.
        assert(asks_of M [<=] (a::A)).  apply H.
        assert(~In a (asks_of (Remove_ab_trades M b a))).
        apply Remove_ab_trades_a_notIn. auto. 
        assert(In a (asks_of M)\/~In a (asks_of M)).
        eauto. destruct H5. apply H. auto.
        apply ttqa_elim in H5. lia. lia.
        assert(asks_of (Remove_ab_trades M b a) [<=] (a::A)).
        eauto. eauto.
      }        
      subst b'. 
      simpl. assert (ttqb M b = (ttq_ab M b a) + (ttqb (Remove_ab_trades M b a) b)).
      apply Remove_ab_trades_correct2b. 
      assert(In b (bids_of M)\/~In b (bids_of M)).
      eauto. destruct H4.
      assert(ttqb M b <= bq b). apply H. auto. lia.
       apply ttqb_elim in H4. lia. subst b'. simpl. auto. 
    }
    split.
    { 
     replace (QM (replace_bid (Remove_ab_trades M b a) b b')) with 
     (QM (Remove_ab_trades M b a)). 
     assert(QM M = QM (Remove_ab_trades M b a) + ttq_ab M b a). 
     apply Remove_ab_trades_QM. lia.
     apply replace_bid_QM.
   }
   split.
   { apply replace_bid_IR. apply Remove_ab_trades_IR. apply H2.
      subst b'. simpl. auto.
   }
   apply replace_bid_NZT.
apply Remove_ab_trades_NZT.
auto.
Qed.









(**************** case when the ask is partially traded *****************************)




Fixpoint replace_ask  (M:list fill_type)(a a':Ask):=
match M with 
|nil => nil
|m::M' =>match (a_eqb a (ask_of m)) with
  |true => (Mk_fill (bid_of m) a' (tq m) (tp m))::replace_ask M' a a'
  |false =>m::replace_ask M' a a'
  end
end.

Lemma replace_ask_elim1 (M:list fill_type)(a a':Ask) :
a=a' -> M = replace_ask M a a'.
Proof.  intros. induction M as [|m' M']. simpl. auto.
simpl. destruct (a_eqb a (ask_of m')) eqn: Hbm'.
simpl. f_equal. subst a'. move /eqP in Hbm'.
subst a. destruct m'. auto. auto. f_equal. auto. Qed.

Lemma replace_ask_elim2 (M:list fill_type)(a a':Ask) :
a<>a' -> ~In a (asks_of (replace_ask M a a')).
Proof.  intros. induction M as [|m' M']. simpl. auto.
simpl. destruct (a_eqb a (ask_of m')) eqn: Hbm'.
simpl. eauto. simpl. intro. destruct H0. move /eqP in Hbm'.
subst a. elim Hbm'. auto. eauto. Qed.


Lemma replace_ask_subset_bid (M:list fill_type)(a a':Ask):
bids_of M = bids_of (replace_ask M a a').
Proof.
revert a a'. induction M as [|m' M']. simpl. auto.
intros. simpl. destruct (a_eqb a (ask_of m')) eqn: Hbm'.
simpl. f_equal. apply IHM'.
simpl. f_equal. apply IHM'. Qed.

Lemma replace_ask_subset_prices (M:list fill_type)(a a':Ask):
trade_prices_of M = trade_prices_of (replace_ask M a a').
Proof.
revert a a'. induction M as [|m' M']. simpl. auto.
intros. simpl. destruct (a_eqb a (ask_of m')) eqn: Hbm'.
simpl. f_equal. apply IHM'.
simpl. f_equal. apply IHM'. Qed.

Lemma replace_ask_subset_asks (M:list fill_type)(a a':Ask)(A:list Ask):
asks_of M [<=] (a::A) -> asks_of (replace_ask M a a') [<=] (a'::A).
Proof.
revert a a' A. induction M as [|m' M']. simpl. auto.
intros. simpl. destruct (a_eqb a (ask_of m')) eqn: Hbm'.
simpl. simpl in H. assert(asks_of M' [<=] a :: A). 
eauto.  eapply IHM' with(a:=a)(a':=a') in H0.
unfold Subset. intros. destruct H1.
simpl. auto. eauto. simpl. simpl in H.
eapply Subset_elim1 in H as H1.
destruct H1. move /eqP in Hbm'. subst a.
elim Hbm'. auto.
eapply Subset_elim2 in H. eapply IHM' with (a:=a)(a':=a') in H.
unfold Subset.
intros. simpl. destruct H1. right. subst a0. auto.
unfold Subset in H. apply H in H1.
destruct H1. left. auto. auto. Qed.

Lemma replace_ask_matchable (M:list fill_type)(a a':Ask):
All_matchable M -> Nat.eqb (sp a) (sp a')-> All_matchable (replace_ask M a a').
Proof. induction M as [|m M']. simpl. auto.
unfold All_matchable.  
simpl. intros. 
destruct (a_eqb a (ask_of m)) eqn: Hm. 
{
  move /eqP in Hm. subst a.
  destruct H1. 
  { subst m0. simpl.
    specialize (H m). 
    destruct H. auto. move /eqP in H0. lia.
    move /eqP in H0. lia. 
  }
  eapply IHM' in H0.
  unfold All_matchable in H0. apply H0 in H1. auto.
  unfold All_matchable. intros. 
  specialize (H m1) as H3. 
  destruct H3. right. auto. auto. lia.
}
{
simpl in H1. destruct H1.
move /eqP in Hm. subst m. auto.
eapply IHM' in H0.  
apply H0 in H1. auto. 
unfold All_matchable. intros.
specialize (H m1) as H3.
destruct H3. auto. auto. lia.
} Qed. 


Lemma replace_ask_ttqa_a_a' (M:list fill_type)(a a':Ask):
~In a' (asks_of M) -> ttqa M a =ttqa (replace_ask M a a') a'.
Proof. induction M as [|m M']. simpl. auto.
simpl. 
destruct (a_eqb a (ask_of m)) eqn: Hm. 
{ simpl. destruct (a_eqb a' a') eqn:Hbb'.
  intros. assert(~ In a' (asks_of M')).
  unfold not in H. auto. apply IHM' in H0. lia.
  move /eqP in Hbb'. elim Hbb'. auto.
}
{ simpl. destruct (a_eqb a' (ask_of m)) eqn:Hbm.
  intros. unfold not in H. 
  move /eqP in Hbm. symmetry in Hbm. 
  destruct H. auto. 
  intros. apply IHM'. auto.
}
Qed. 



Lemma replace_ask_ttqa_a0 (M:list fill_type)(a a' a0:Ask):
a0<>a'/\a0<>a -> ttqa M a0 = ttqa (replace_ask M a a') a0.
Proof. induction M as [|m M']. simpl. auto.
simpl. 
destruct (a_eqb a0 (ask_of m)) eqn: Hm. 
{ simpl. destruct (a_eqb a (ask_of m)) eqn:Hbm.
  intros. destruct H. 
  move /eqP in Hbm. move /eqP in Hm. 
  subst. elim H0. auto. 
  intros. destruct H. simpl.
  rewrite Hm. rewrite IHM'.
  auto. lia. 
}
{ destruct (a_eqb a (ask_of m)) eqn:Hbm.
  intros. simpl. destruct H. 
  destruct (a_eqb a0 a') eqn:Hb.
  move /eqP in Hb. subst. elim H. auto. 
  apply IHM'. auto. simpl.
  rewrite Hm. auto. 
}
Qed.
 
Lemma replace_ask_ttqb (M:list fill_type)(b:Bid)(a a':Ask):
ttqb M b = ttqb (replace_ask M a a') b.
Proof. induction M as [|m M']. simpl. auto.
simpl. 
destruct (b_eqb b (bid_of m)) eqn: Hm. 
{ destruct (a_eqb a (ask_of m)) eqn:Hbm.
  simpl. rewrite Hm. lia. 
  simpl.
  rewrite Hm. lia.
}
{ destruct (a_eqb a (ask_of m)) eqn:Hbm.
  simpl. rewrite Hm. lia. 
  simpl.
  rewrite Hm. lia.
}
Qed.

Lemma replace_ask_Uniform (M:list fill_type)(a a':Ask):
Uniform M -> Uniform (replace_ask M a a').
Proof. unfold Uniform. 
assert(trade_prices_of M = trade_prices_of (replace_ask M a a')).
eapply replace_ask_subset_prices.
rewrite H. auto. Qed.


Lemma replace_ask_IR (M:list fill_type)(a a':Ask):
Is_IR M -> a' <= a -> Is_IR (replace_ask M a a').
Proof. induction M as [|m M']. simpl. auto.
unfold Is_IR.  
simpl. intros. 
destruct (a_eqb a (ask_of m)) eqn: Hm. 
{
  move /eqP in Hm. subst a.
  destruct H1. 
  { subst m0. unfold rational.
    simpl.
    specialize (H m). 
    destruct H. auto. 
    lia.
  }
  eapply IHM' in H0.
  unfold Is_IR in H0. apply H0 in H1. auto.
  unfold Is_IR. intros. 
  specialize (H m1) as H3. 
  destruct H3. right. auto. auto.
}
{
simpl in H1. destruct H1.
move /eqP in Hm. subst m. auto.
eapply IHM' in H0.  
apply H0 in H1. auto. 
unfold Is_IR. intros.
specialize (H m1) as H3.
destruct H3. auto. auto. 
} Qed. 

Lemma replace_ask_QM (M:list fill_type)(a a':Ask):
QM(M) = QM(replace_ask M a a').
Proof. induction M as [|m M']. simpl. auto.
simpl. destruct (a_eqb a (ask_of m)) eqn: Hm. simpl. lia.
simpl. lia. Qed.

Lemma replace_ask_NZT (M:list fill_type)(a a':Ask)
(NZT:forall m : fill_type, In m M -> tq m > 0):
(forall m : fill_type, In m (replace_ask M a a') -> tq m > 0).
Proof. induction M as [|m M']. simpl. auto.
simpl. destruct (a_eqb a (ask_of m)) eqn: Hm. simpl.
intros. destruct H. subst m0. simpl. eauto.
apply IHM'. eauto. auto. 
simpl. intros. destruct H. subst m0.
apply NZT. eauto. apply IHM'.
eauto. auto. Qed.

Lemma replace_ask_matching1 (M:list fill_type)(B:list Bid)(A:list Ask)(a a':Ask)
(NDA:NoDup (a'::A)):
matching_in B (a::A) M-> ttqa M a <= sq a' -> Nat.eqb (sp a) (sp a') ->
matching_in B (a'::A) (replace_ask M a a').
Proof. intros.  split.
{ split. 
  { apply replace_ask_matchable. apply H. auto. }
  { split. 
    {
    intros. replace (ttqb (replace_ask M a a') b) with (ttqb M b).
    assert(In b (bids_of M)\/~In b (bids_of M)).
    eauto. destruct H3. apply H. auto.
    apply ttqb_elim in H3. lia. apply replace_ask_ttqb.
    }
    { intros. destruct (a_eqb a a') eqn:Hbb'.
      { move /eqP in Hbb'. apply replace_ask_elim1 with (M:=M) in Hbb'.
        rewrite <- Hbb'. assert(In a0 (asks_of M)\/~In a0 (asks_of M)).
        eauto. destruct H3. apply H. auto.
        apply ttqa_elim in H3. lia.
      }
      { destruct (a_eqb a0 a') eqn:Hb0b';destruct (a_eqb a0 a) eqn:Hb0b.
        {
          move /eqP in Hb0b'. move /eqP in Hb0b.
          move /eqP in Hbb'. subst. elim Hbb'. auto.
        }
        {
          move /eqP in Hbb'. apply replace_ask_elim2 with (M:=M) in Hbb'.
          move /eqP in Hb0b'. subst. replace (ttqa (replace_ask M a a') a')
          with (ttqa M a). auto. apply replace_ask_ttqa_a_a'.
          assert((asks_of M)[<=](a::A)). apply H. intro.
          assert(In a' (a :: A)). eauto. destruct H5. 
          move /eqP in Hb0b. subst. elim Hb0b. auto.
          apply nodup_elim2 in NDA. eauto.
        }
        {
          move /eqP in Hbb'. apply replace_ask_elim2 with (M:=M) in Hbb'.
          move /eqP in Hb0b. subst. unfold not in Hbb'. 
          apply Hbb' in H2. elim H2.
        }
        {
          move /eqP in Hb0b'. move /eqP in Hb0b.
          move /eqP in Hbb'. replace (ttqa (replace_ask M a a') a0) 
          with (ttqa M a0). assert(In a0 (asks_of M)\/~In a0 (asks_of M)).
          eauto. destruct H3. apply H. auto.
          apply ttqa_elim in H3. lia.
          eapply replace_ask_ttqa_a0. auto.
         }
       }
    }
  }
}
{
  split.
  { rewrite <- replace_ask_subset_bid. apply H. }
  { apply replace_ask_subset_asks. apply H. }

} Qed.


Lemma exists_M0_reduced_ask_matching (M:list fill_type)(B:list Bid)(A:list Ask)(b:Bid)(a:Ask)
(NDA:NoDup (idas_of (a::A)))
(NZT:forall m : fill_type, In m M -> tq m > 0):
matching_in (b::B) (a::A) M-> 
ttq_ab M b a = (bq b) ->
((sq a) > (bq b)) -> 
Is_IR M ->
exists M0, (matching_in B
((Mk_ask (sp a) (stime a) (sq a - (bq b)) (ida a))::A) M0)
/\(QM(M)=QM(M0) + (bq b)/\Is_IR M0/\
(forall m : fill_type, In m M0 -> tq m > 0)).
Proof. intros. 
set (a':={| sp := a; stime := stime a; sq := sq a - bq b; ida := ida a |}).
exists (replace_ask (Remove_ab_trades M b a) a a').
split. { apply replace_ask_matching1. apply idas_of_nodup. simpl.
      simpl in NDA. auto.
      { split. (*Proof that matching *)
        split.
        apply Remove_ab_trades_matchable. apply H.
        split. 
        { intros. assert(ttqb (Remove_ab_trades M b a) b0 <= ttqb M b0).
          apply Remove_ab_trades_ttq_le_b.
          assert(ttqb M b0 <= bq b0). 
          assert(In b0 (bids_of M)\/~In b0 (bids_of M)).
          eauto. destruct H5. apply H. auto.
          apply ttqb_elim in H5. lia. lia.
        }
        { intros. assert(ttqa (Remove_ab_trades M b a) a0 <= ttqa M a0).
          apply Remove_ab_trades_ttq_le_a.
          assert(ttqa M a0 <= sq a0). 
          assert(In a0 (asks_of M)\/~In a0 (asks_of M)).
          eauto. destruct H5. apply H. auto.
          apply ttqa_elim in H5. lia. lia.
        }
        split. 
        { assert(bids_of (Remove_ab_trades M b a) [<=] bids_of M).
          apply Remove_ab_trades_bids_subset.
          assert(bids_of M [<=] (b::B)).  apply H.
          assert(~In b (bids_of (Remove_ab_trades M b a))).
          apply Remove_ab_trades_b_notIn. auto. 
          assert(In b (bids_of M)\/~In b (bids_of M)).
          eauto. destruct H5. apply H. auto.
          apply ttqb_elim in H5. lia. lia.
          assert(bids_of (Remove_ab_trades M b a) [<=] (b::B)).
          eauto. eauto.
        }
        { assert(asks_of (Remove_ab_trades M b a) [<=] asks_of M).
          apply Remove_ab_trades_asks_subset.
          assert(asks_of M [<=] (a::A)). apply H.
          eauto.
        }        
      }        
      subst a'. 
      simpl. assert (ttqa M a = (ttq_ab M b a) + (ttqa (Remove_ab_trades M b a) a)).
      apply Remove_ab_trades_correct2a. 
      assert(In a (asks_of M)\/~In a (asks_of M)).
      eauto. destruct H4.
      assert(ttqa M a <= sq a). apply H. auto. lia.
       apply ttqa_elim in H4. lia. subst a'. simpl. auto. 
    }
    split.
    { 
     replace (QM (replace_ask (Remove_ab_trades M b a) a a')) with 
     (QM (Remove_ab_trades M b a)). 
     assert(QM M = QM (Remove_ab_trades M b a) + ttq_ab M b a). 
     apply Remove_ab_trades_QM. lia.
     apply replace_ask_QM.
   }
   split.
   { apply replace_ask_IR. apply Remove_ab_trades_IR. apply H2.
      subst a'. simpl. auto.
   }
   apply replace_ask_NZT.
apply Remove_ab_trades_NZT.
auto.
Qed.





Lemma exists_M0_reduced_ask_uniform (M:list fill_type)(B:list Bid)(A:list Ask)(b:Bid)(a:Ask)
(NDA:NoDup (idas_of (a::A)))
(NZT:forall m : fill_type, In m M -> tq m > 0):
Is_uniform M (b::B) (a::A) -> 
ttq_ab M b a = (bq b) ->
((sq a) > (bq b)) -> 
exists M0, (Is_uniform M0 B
((Mk_ask (sp a) (stime a) (sq a - (bq b)) (ida a))::A))
/\(QM(M)=QM(M0) + (bq b)/\
(forall m : fill_type, In m M0 -> tq m > 0)).
Proof. intros. 
set (a':={| sp := a; stime := stime a; sq := sq a - bq b; ida := ida a |}).
exists (replace_ask (Remove_ab_trades M b a) a a').
split. 
  { split.
    { apply replace_ask_Uniform. apply Remove_ab_trades_Uniform. apply H. }
    split. 
{ apply replace_ask_matching1. apply idas_of_nodup. simpl.
      simpl in NDA. auto.
      { split. (*Proof that matching *)
        split.
        apply Remove_ab_trades_matchable. apply H.
        split. 
        { intros. assert(ttqb (Remove_ab_trades M b a) b0 <= ttqb M b0).
          apply Remove_ab_trades_ttq_le_b.
          assert(ttqb M b0 <= bq b0). 
          assert(In b0 (bids_of M)\/~In b0 (bids_of M)).
          eauto. destruct H4. apply H. auto.
          apply ttqb_elim in H4. lia. lia.
        }
        { intros. assert(ttqa (Remove_ab_trades M b a) a0 <= ttqa M a0).
          apply Remove_ab_trades_ttq_le_a.
          assert(ttqa M a0 <= sq a0). 
          assert(In a0 (asks_of M)\/~In a0 (asks_of M)).
          eauto. destruct H4. apply H. auto.
          apply ttqa_elim in H4. lia. lia.
        }
        split. 
        { assert(bids_of (Remove_ab_trades M b a) [<=] bids_of M).
          apply Remove_ab_trades_bids_subset.
          assert(bids_of M [<=] (b::B)).  apply H.
          assert(~In b (bids_of (Remove_ab_trades M b a))).
          apply Remove_ab_trades_b_notIn. auto. 
          assert(In b (bids_of M)\/~In b (bids_of M)).
          eauto. destruct H4. apply H. auto.
          apply ttqb_elim in H4. lia. lia.
          assert(bids_of (Remove_ab_trades M b a) [<=] (b::B)).
          eauto. eauto.
        }
        { assert(asks_of (Remove_ab_trades M b a) [<=] asks_of M).
          apply Remove_ab_trades_asks_subset.
          assert(asks_of M [<=] (a::A)). apply H.
          eauto.
        }        
      }        
      subst a'. 
      simpl. assert (ttqa M a = (ttq_ab M b a) + (ttqa (Remove_ab_trades M b a) a)).
      apply Remove_ab_trades_correct2a. 
      assert(In a (asks_of M)\/~In a (asks_of M)).
      eauto. destruct H3.
      assert(ttqa M a <= sq a). apply H. auto. lia.
       apply ttqa_elim in H3. lia. subst a'. simpl. auto. 
    }
   { apply replace_ask_IR. apply Remove_ab_trades_IR. apply H.
      subst a'. simpl. auto.
   }
   }
   split.
    { 
     replace (QM (replace_ask (Remove_ab_trades M b a) a a')) with 
     (QM (Remove_ab_trades M b a)). 
     assert(QM M = QM (Remove_ab_trades M b a) + ttq_ab M b a). 
     apply Remove_ab_trades_QM. lia.
     apply replace_ask_QM.
   }
   apply replace_ask_NZT.
   apply Remove_ab_trades_NZT.
   auto.
Qed.

End Transform.