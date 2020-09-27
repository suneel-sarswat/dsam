

(* -----------------Description------------------------------------------------------

This file contains basic definitions of Bids, Asks and Fill (trade between
Bid and Ask). These data types are also attached with eqType (i.e, domain 
with decidable Equality). We also define projection functions on list
of Bids and Asks.

    Terms          <==>     Explanations
    Bid                     Type for a buy request
    Ask                     Type for an sell request
    fill_type               Type for trade output

    bid_prices B            projection of bid prices in B
    ask_prices A            projection of ask prices in A
    bids_of F               projection of bids in F
    asks_of F               projection of asks in F
 

Some important results:

  Lemma included_M_imp_included_bids : included M1 M2 -> included (bids_of M1) (bids_of M2).
  Lemma bids_of_perm: perm M M' -> perm (bids_of M) (bids_of M').

  Lemma included_M_imp_included_asks : included M1 M2 -> included (asks_of M1) (asks_of M2).
  Lemma asks_of_perm: perm M M' -> perm (asks_of M) (asks_of M').

  Lemma included_M_imp_included_tps: included M M'->included(trade_prices_of M)(trade_prices_of M').
  Lemma tps_of_perm : perm M M' -> perm (trade_prices_of M) (trade_prices_of M').

 ---------------------------------------------------------------------------------------- *)


Require Import ssreflect ssrbool.
Require Export Lists.List.
Require Export GenReflect SetSpecs.
Require Export DecList DecType MoreDecList.

  
Section BidAsk.

Record Bid:Type:= Mk_bid{
                        bp:> nat;
                        btime: nat;
                        bq: nat;
                        idb: nat}.



Definition b_eqb (x y:Bid): bool:= (idb x == idb y)&& (btime x == btime y) &&(bq x == bq y) && ( bp x == bp y).

 
Record Ask:Type:= Mk_ask{
                        sp:>nat;
                        stime: nat;
                        sq: nat;
                        ida: nat;}.

Definition a_eqb (x y: Ask): bool:= (ida x == ida y) && (stime x == stime y) && (sq x == sq y) && (  sp x ==  sp y).

(*
Hypothesis unique_idb : forall b1 b2:Bid, (idb(b1) = idb(b2))-> (b1 = b2).
Hypothesis unique_ida : forall a1 a2:Ask, (ida(a1) = ida(a2))-> (a1 = a2).
*)

(*----------------  Attaching Bid to the EqType ----------------------------------*)

Lemma b_eqb_ref (x:Bid): b_eqb x x = true.
Proof. unfold b_eqb. split_. split_. split_. all:apply /eqP;auto.  Qed.

Hint Resolve b_eqb_ref: auction.
Lemma b_eqb_elim (x y:Bid):  b_eqb x y -> x = y.
Proof. { unfold b_eqb. move /andP. intro H. destruct H as [H1 H2].
         move /andP in H1.
         destruct H1 as [H1 H3]. move /andP in H1. destruct H1 as [H1 H4].
         destruct x; destruct y. move /eqP in H1. simpl in H1.  
         simpl in H3. simpl in H2. simpl in H4. move /eqP in H2. move /eqP in H3. move /eqP in H4.
         subst bp0. subst bq0. subst idb0.  subst btime0. auto.  } Qed. 


Lemma b_eqb_intro (x y:Bid): x=y -> b_eqb x y = true.
Proof. { unfold b_eqb. intros H. split_. split_. split_. 
         all:apply /eqP;subst x;auto. } Qed.  

Hint Immediate b_eqb_elim b_eqb_intro: auction.

Lemma b_eqP (x y:Bid): reflect (x=y)(b_eqb x y).
Proof. apply reflect_intro. split; auto with auction. Qed. 
Hint Resolve b_eqP: auction.


Canonical bid_eqType: eqType:= {| Decidable.E:= Bid; Decidable.eqb:= b_eqb; Decidable.eqP:= b_eqP |}.



(*------------------ Attaching Ask to EqType ------------------------------------ *)

Lemma a_eqb_ref (x: Ask): a_eqb x x = true.
Proof. { unfold a_eqb. split_. split_. split_. all:apply /eqP;auto. } Qed.


Hint Resolve a_eqb_ref: auction.
Lemma a_eqb_elim (x y: Ask):  a_eqb x y -> x = y.
Proof. { unfold a_eqb. move /andP. intro H. destruct H as [H1 H2].
         move /andP in H1.
         destruct H1 as [H1 H3]. move /andP in H1.
         destruct H1 as [H1 H4].
         destruct x; destruct y. move /eqP in H1. simpl in H1.  
         simpl in H3. simpl in H2. simpl in H4. move /eqP in H2. move /eqP in H3.
         move /eqP in H4. subst sp0. subst sq0. subst ida0. subst stime0. auto. } Qed. 


Lemma a_eqb_intro (x y: Ask): x=y -> a_eqb x y = true.
Proof. { unfold a_eqb. intros H. split_. split_. split_.
         all:apply /eqP;subst x;auto. } Qed.  

Hint Immediate a_eqb_elim a_eqb_intro: auction.

Lemma a_eqP (x y: Ask): reflect (x=y)(a_eqb x y).
Proof. apply reflect_intro. split; auto with auction. Qed. 
Hint Resolve a_eqP: auction.

Canonical ask_eqType: eqType:= {| Decidable.E:= Ask; Decidable.eqb:= a_eqb; Decidable.eqP:= a_eqP |}.

(*------------- Price projections for list of Bids and Asks--------------------------*)

Fixpoint bid_prices (B: list Bid): (list nat):=
  match B with
  |nil => nil
  |b::B' => (bp b)::(bid_prices B')
  end.

Lemma bid_prices_intro (B: list Bid) (b: Bid):
  In b B -> (In (bp b) (bid_prices B)).
Proof. { intro H. induction B. simpl. simpl in H. contradiction.
         destruct  H. subst b. simpl. left. auto. simpl. right. auto. } Qed.


Lemma bid_prices_elim (B: list Bid): forall p, In p (bid_prices B)->
                                             exists b, In b B /\ p = bp b.
Proof. { intros p H. induction B. simpl in H. contradiction. simpl in H.
       destruct  H as [H1 | H2].  exists a. split; auto.
       apply IHB in H2 as H0. destruct H0 as [b H0].
       exists b. destruct H0. split.
       eauto. auto. } Qed.

Lemma bid_prices_intro1 (B: list Bid) (B': list Bid):
  B [<=] B' -> ((bid_prices B)  [<=] (bid_prices B')).
Proof. { intro H. intros p. intro H1. assert (H2: exists b, In b B /\ p=bp b).
         apply bid_prices_elim. exact. destruct H2. destruct H0.
         assert (H3: In x B'). auto. subst p. eapply bid_prices_intro. exact. } Qed.

Fixpoint bid_quantities (B: list Bid): (list nat):=
  match B with
  |nil => nil
  |b::B' => (bq b)::(bid_quantities B')
  end.

Lemma bid_quantities_intro (B: list Bid) (b: Bid):
  In b B -> (In (bq b) (bid_quantities B)).
Proof. { intro H. induction B. simpl. simpl in H. contradiction.
         destruct  H. subst b. simpl. left. auto. simpl. right. auto. } Qed.


Lemma bid_quantities_elim (B: list Bid): forall q, In q (bid_quantities B)->
                                             exists b, In b B /\ q = bq b.
Proof. { intros p H. induction B. simpl in H. contradiction. simpl in H.
       destruct  H as [H1 | H2].  exists a. split; auto.
       apply IHB in H2 as H0. destruct H0 as [b H0].
       exists b. destruct H0. split.
       eauto. auto. } Qed.

Lemma bid_quantities_intro1 (B: list Bid) (B': list Bid):
  B [<=] B' -> ((bid_quantities B)  [<=] (bid_quantities B')).
Proof. { intro H. intros q. intro H1. assert (H2: exists b, In b B /\ q=bq b).
         apply bid_quantities_elim. exact. destruct H2. destruct H0.
         assert (H3: In x B'). auto. subst q. eapply bid_quantities_intro. exact. } Qed.




Fixpoint ask_prices (A: list Ask): (list nat):=
  match A with
  |nil => nil
  |a::A' => (sp a)::(ask_prices A')
  end.

Lemma ask_prices_intro (A: list Ask) (a: Ask):
  In a A -> (In (sp a) (ask_prices A)).
Proof. { intro H. induction A. simpl. simpl in H. contradiction.
         destruct  H. subst a. simpl. left. auto. simpl. right. auto. } Qed.

Lemma ask_prices_elim (A: list Ask): forall p, In p (ask_prices A)->
                                             exists a, In a A /\ p = sp a.
Proof. { intros p H. induction A. simpl in H. contradiction. simpl in H.
       destruct  H as [H1 | H2]. exists a. split; auto.
       apply IHA in H2 as H0. destruct H0 as [a0 H0].
       exists a0. destruct H0. split.
       eauto. auto. } Qed.

Lemma ask_prices_intro1 (A: list Ask) (A': list Ask):
  A [<=] A' -> ((ask_prices A)  [<=] (ask_prices A')).
Proof.  { intro H. intros p. intro H1. assert (H2: exists a, In a A /\ p=sp a).
          apply ask_prices_elim. exact. destruct H2. destruct H0.
          assert (H3: In x A'). eauto. subst p. eapply ask_prices_intro. exact. } Qed.




Hint Resolve bid_prices_elim bid_prices_intro bid_prices_intro1: core.
Hint Resolve ask_prices_elim ask_prices_intro ask_prices_intro1: core.


(* ------------definition of  fill_type as record---------------------------- *)

Record fill_type:Type:=  Mk_fill {
                             bid_of: Bid;
                             ask_of: Ask;
                             tq: nat;
                             tp: nat }. 
                             
 Definition m_eqb (x y: fill_type): bool:= (bid_of x == bid_of y) && (  ask_of x ==  ask_of y) && (tq x == tq y) && (tp x == tp y).                            

(*------------------ Attaching fill_type to eqType ------------------------------------ *)

Lemma m_eqb_ref (x: fill_type): m_eqb x x = true.
Proof. unfold m_eqb. apply /andP. split. apply /andP. split. apply /andP. split. all: apply /eqP; auto. Qed.


Hint Resolve m_eqb_ref: auction.
Lemma m_eqb_elim (x y: fill_type):  m_eqb x y -> x = y.
Proof. { unfold m_eqb. destruct x. destruct y. simpl. intros. move /andP in H.
         destruct H. move /andP in H. destruct H. move /andP in H. destruct H. 
         move /eqP in H. move /eqP in H1. move /eqP in H2.
         move /eqP in H0. rewrite H0. rewrite H1. rewrite H. rewrite H2. auto. } Qed.


Lemma m_eqb_intro (x y: fill_type): x=y -> m_eqb x y = true.
Proof. { unfold m_eqb. intros H. apply /andP. split. apply /andP. 
         split. apply /andP. 
         split. apply /eqP. subst x. exact. apply /eqP. subst x. exact. apply /eqP. 
         subst x. exact. apply /eqP. 
         subst x. exact. } Qed.  

Hint Immediate m_eqb_elim m_eqb_intro: auction.

Lemma m_eqP (x y: fill_type): reflect (x=y)(m_eqb x y).
Proof. apply reflect_intro. split; auto with auction. Qed. 
Hint Resolve m_eqP: auction.

Canonical fill_eqType: eqType:= {| Decidable.E:= fill_type; Decidable.eqb:= m_eqb; Decidable.eqP:= m_eqP |}.




Fixpoint bids_of (F: list fill_type) : (list Bid) :=
  match F with
  |nil => nil
  |f::F'=> (bid_of f)::(bids_of F')
  end.



Lemma bids_of_intro (F: list fill_type) (m: fill_type):
  In m F -> (In (bid_of m) (bids_of F)).
Proof. { intro H. induction F. simpl. simpl in H. contradiction. destruct  H.
        subst m. simpl. left. auto. simpl. right. auto. } Qed.

Lemma bids_of_nonempty (F: list fill_type):
  F<>nil -> (bids_of F)<>nil.
Proof. intros. induction F. destruct H. auto. simpl. 
apply non_nil_size. simpl. lia. Qed.

Lemma bids_of_elim0 (F: list fill_type) (m: fill_type):
In m F -> In (bid_of m) (bids_of F).
Proof. { induction F as [| a F']. simpl. auto.
         intros. simpl. simpl in H. destruct H.
         left. subst a. auto. right. apply IHF'. exact. } Qed.

Lemma bids_of_delete (F: list fill_type) (m: fill_type):
  In m F -> NoDup (bids_of F) -> (bids_of (delete m F)) = (delete (bid_of m) (bids_of F)).
Proof. { induction F as [| a F']. { simpl. auto. }
         { intros. simpl. 
           destruct (m_eqb m a) eqn: Hma.
          { assert (Ht: (b_eqb (bid_of m) (bid_of a))=true).
            move /eqP in Hma. apply /eqP. subst m. auto.
            rewrite Ht. auto. } 
            { destruct (b_eqb (bid_of m) (bid_of a)) eqn: Ham.
              { move /eqP in Ham. simpl. rewrite IHF'. 
                move /eqP in Hma. eapply element_list with (b:=m)(a:=a). auto. exact.
                 eauto. simpl in H.  destruct H. move /eqP in Hma.
                apply eq_sym ; trivial. subst a. destruct Hma. auto. 
                assert (Hbid: ~In (bid_of a) (bids_of F')).  eauto. 
                assert (Hbidm: In (bid_of m) (bids_of F')). apply bids_of_elim0. exact. 
                rewrite Ham in Hbidm. contradiction. }
               { simpl. rewrite IHF'. move /eqP in Hma.
                 destruct H. symmetry in H. contradiction. exact. 
                 eauto. auto. }}}} Qed.
          
Lemma bids_of_elim (F: list fill_type): forall b, In b (bids_of F)->
                                             exists m, In m F /\ b = bid_of m.
Proof. { intros b H. induction F. simpl in H. contradiction. simpl in H.
       destruct  H as [H1 | H2]. exists a. split; auto.
       apply IHF in H2 as H0. destruct H0 as [m H0]. exists m. destruct H0. split.
       eauto. auto. } Qed.



Lemma bids_of_intro1 (M': list fill_type) (M: list fill_type):
  M [<=] M' -> ((bids_of M)  [<=] (bids_of M')).
Proof.  { intro H. intros b. intro H1. assert (H2: exists m, In m M /\ b=bid_of m).
          apply bids_of_elim. exact. destruct H2. destruct H0. assert (H3: In x M').
          auto. subst b. eapply bids_of_intro. exact. } Qed.


Lemma bids_of_elim1 (M: list fill_type)(m: fill_type)(b: Bid): In b (bids_of (delete m M)) ->
                                                               In b (bids_of M).
Proof. { induction M. simpl. auto. simpl. intros. case (m_eqb m a) eqn: Hm.
         right. exact. simpl in H. destruct H. left. exact. apply IHM in H. right. exact. } Qed.

Lemma count_in_deleted_bids (m: fill_type)(M: list fill_type):
  In m M -> count (bid_of m) (bids_of M) = S (count (bid_of m) (bids_of (delete m M))).
Proof. { induction M.
       { simpl. auto. }
       { intro h1. destruct (m == a) eqn: h2.
         { simpl. rewrite h2. move /eqP in h2.
           subst a. simpl. replace (b_eqb (bid_of m) (bid_of m)) with true. auto. auto. }
         { assert (h1a: In m M).
           { move /eqP in h2. eapply element_list with (b:=m)(a:=a). auto. exact. }
           replace (delete m (a :: M)) with (a :: (delete m M)).
           { simpl. destruct (b_eqb (bid_of m) (bid_of a)) eqn: h3.
             { apply IHM in h1a as h1b. rewrite h1b. auto. }
             { auto. } }
           { simpl. rewrite h2. auto. } } } } Qed.


Lemma included_M_imp_included_bids (M1 M2: list fill_type): included M1 M2 ->
                                                    included (bids_of M1) (bids_of M2).
Proof. { revert M2. induction M1 as [| m1].
       { simpl. auto. }
       { intros M2 h1.
         assert (h2: In m1 M2). eauto.
         assert (h3: included M1 (delete m1 M2)). eauto.
         assert (h3a: included (bids_of M1) (bids_of (delete m1 M2))).
         { auto. }
         assert(h4:count (bid_of m1)(bids_of M2)= S (count (bid_of m1) (bids_of (delete m1 M2)))).
         { eauto using count_in_deleted_bids. }
         eapply included_intro.
         intro x.  simpl. destruct (b_eqb x (bid_of m1)) eqn: C1.
         { (* ---- C1: x = b1 ---- *)
           move /b_eqP in C1. subst x.
           rewrite h4.
           eapply included_elim in h3a  as h3b. instantiate (1 := bid_of m1) in h3b.
           lia. }
         { (*----- C1: x <> b1 ---- *)
           assert (h3b: included M1 M2). eapply included_elim4; apply h1. 
           apply IHM1 in h3b as h3c. auto. } } } Qed.


       
Lemma bids_of_perm (M M': list fill_type): perm M M' -> perm (bids_of M) (bids_of M').
Proof. { intro H. unfold perm in H. move /andP in H. destruct H.
         unfold perm. apply /andP. split. all: eapply included_M_imp_included_bids;exact. } Qed.

Lemma bids_of_nodup (F: list fill_type): NoDup (bids_of F) -> NoDup F.
Proof. { intro H. induction F. auto. assert (H1:NoDup (bids_of F)).
         simpl in H. eauto. apply IHF in H1 as H2. simpl in H. 
         assert (~In (bid_of a) (bids_of F)). eauto. 
         assert (~In a (F)). intro.  assert (H4:In (bid_of a) (bids_of F)).
         apply bids_of_elim0. exact. contradiction. eauto. } Qed.
 
Lemma bids_of_delete_delete (F: list fill_type) (m1 m2: fill_type):
  In m1 F -> In m2 F -> NoDup (bids_of F) -> 
(bids_of (delete m1 (delete m2 F))) = (delete (bid_of m1) (delete (bid_of m2) (bids_of F))).
Proof. { intros. assert (Hm1m2: m1=m2\/m1<>m2). eapply reflect_EM. auto.
       destruct Hm1m2.  
       { subst m1. simpl. assert (H2:(delete m2 (delete m2 F)) = delete m2 F).
         { assert (H3:~In m2 (delete m2 F) ). { apply delete_intro2. apply bids_of_nodup.
         exact. } apply delete_intro1 in H3. auto. } 
         assert (H3:(delete (bid_of m2) (delete (bid_of m2) (bids_of F))) = (delete (bid_of m2) (bids_of F))).
         { assert (H4:~In (bid_of m2) (delete (bid_of m2) (bids_of F))). { apply delete_intro2.  exact. } apply delete_intro1 in H4. auto. }
         rewrite H2. rewrite H3. apply bids_of_delete. exact. exact. }
       { assert (H3: (bids_of (delete m2 F)) = (delete (bid_of m2) (bids_of F))).
         apply bids_of_delete. exact. exact.
         assert (H4: (bids_of (delete m1 (delete m2 F))) = 
         (delete (bid_of m1) ((delete (bid_of m2) (bids_of F))))).
         rewrite <- H3. apply bids_of_delete. apply delete_intro. exact.  exact.   
         { assert (H4: (bids_of (delete m2 F)) = delete (bid_of m2) (bids_of F)).
           apply bids_of_delete. exact. exact. rewrite H4. eauto. } exact. }} Qed.
         
     

Fixpoint asks_of (F: list fill_type) : (list Ask) :=
  match F with
  |nil => nil
  |f::F'=> (ask_of f)::(asks_of F')
  end.

Lemma asks_of_intro (F: list fill_type) (m: fill_type):
  In m F -> (In (ask_of m) (asks_of F)).
Proof. { intro H. induction F. simpl. simpl in H. contradiction. destruct  H.
         subst m. simpl. left. auto. simpl. right. auto. } Qed.

Lemma asks_of_nonempty (F: list fill_type):
  F<>nil -> (asks_of F)<>nil.
Proof. intros. induction F. destruct H. auto. simpl. 
apply non_nil_size. simpl. lia. Qed.

Lemma asks_of_elim0 (F: list fill_type) (m: fill_type):
In m F -> In (ask_of m) (asks_of F).
Proof. { induction F as [| a F']. simpl. auto.
         intros. simpl. simpl in H. destruct H.
         left. subst a. auto. right. apply IHF'. exact. } Qed.
(*TODO: automate the following Lemma*)
Lemma asks_of_delete (F: list fill_type) (m: fill_type):
  In m F -> NoDup (asks_of F) -> (asks_of (delete m F)) = (delete (ask_of m) (asks_of F)).
Proof. { induction F as [| a F']. { simpl. auto. }
         { intros. simpl. 
           destruct (m_eqb m a) eqn: Hma.
          { assert (Ht: (a_eqb (ask_of m) (ask_of a))=true).
            move /eqP in Hma. apply /eqP. subst m. auto.
            rewrite Ht. auto. } 
            { destruct (a_eqb (ask_of m) (ask_of a)) eqn: Ham.
              { move /eqP in Ham. simpl. rewrite IHF'. 
                move /eqP in Hma. 
                destruct H. symmetry in H. contradiction. exact.
                eauto. simpl in H.  destruct H. move /eqP in Hma.
                apply eq_sym ; trivial. subst a. destruct Hma. auto. 
                assert (Hask: ~In (ask_of a) (asks_of F')).  eauto. 
                assert (Haskm: In (ask_of m) (asks_of F')). apply asks_of_elim0. exact. 
                rewrite Ham in Haskm. contradiction. }
               { simpl. rewrite IHF'. move /eqP in Hma.
                 destruct H. symmetry in H. contradiction. exact. 
                 eauto. auto. }}}} Qed.
  
Lemma asks_of_elim (F: list fill_type): forall a, In a (asks_of F)->
                                            exists m, In m F /\ a = ask_of m.
Proof. { intros b H. induction F. simpl in H. contradiction. simpl in H. 
       destruct  H as [H1 | H2]. exists a. split; auto.
       apply IHF in H2 as H0. destruct H0 as [m H0]. exists m. destruct H0. split.
       eauto. auto. } Qed.
       
Lemma asks_of_intro1 (M': list fill_type) (M: list fill_type):
  M [<=] M' -> ((asks_of M)  [<=] (asks_of M')).
Proof.  { intro H. intros a. intro H1. assert (H2: exists m, In m M /\ a=ask_of m).
          apply asks_of_elim. exact. destruct H2. destruct H0. assert (H3: In x M').
          auto. subst a. eapply asks_of_intro. exact. } Qed.

Lemma asks_of_elim1 (M: list fill_type)(m: fill_type)(a: Ask): In a (asks_of (delete m M)) ->
                                                               In a (asks_of M).
Proof. { induction M. simpl. auto. simpl. intros. case (m_eqb m a0) eqn: Hm.
         right. exact. simpl in H. destruct H. left. exact. apply IHM in H.
         right. exact. } Qed.


Lemma count_in_deleted_asks (m: fill_type)(M: list fill_type):
  In m M -> count (ask_of m) (asks_of M) = S (count (ask_of m) (asks_of (delete m M))).
Proof. { induction M.
       { simpl. auto. }
       { intro h1. destruct (m == a) eqn: h2.
         { simpl. rewrite h2. move /eqP in h2.
           subst a. simpl. replace (a_eqb (ask_of m) (ask_of m)) with true. auto. auto. }
         { assert (h1a: In m M).
           { move /eqP in h2. eapply element_list with (b:=m)(a:=a). auto. exact. }
           replace (delete m (a :: M)) with (a :: (delete m M)).
           { simpl. destruct (a_eqb (ask_of m) (ask_of a)) eqn: h3.
             { apply IHM in h1a as h1b. rewrite h1b. auto. }
             { auto. } }
           { simpl. rewrite h2. auto. } } } } Qed.


Lemma included_M_imp_included_asks (M1 M2: list fill_type): included M1 M2 ->
                                                    included (asks_of M1) (asks_of M2).
Proof. { revert M2. induction M1 as [| m1].
       { simpl. auto. }
       { intros M2 h1.
         assert (h2: In m1 M2). eauto.
         assert (h3: included M1 (delete m1 M2)). eauto.
         assert (h3a: included (asks_of M1) (asks_of (delete m1 M2))).
         { auto. }
         assert(h4:count (ask_of m1)(asks_of M2)= S (count (ask_of m1) (asks_of (delete m1 M2)))).
         { eauto using count_in_deleted_asks. }
         eapply included_intro.
         intro x.  simpl. destruct (a_eqb x (ask_of m1)) eqn: C1.
         { (* ---- C1: x = b1 ---- *)
           move /a_eqP in C1. subst x.
           rewrite h4.
           eapply included_elim in h3a  as h3b. instantiate (1 := ask_of m1) in h3b.
           lia. }
         { (*----- C1: x <> b1 ---- *)
           assert (h3b: included M1 M2). eapply included_elim4; apply h1. 
           apply IHM1 in h3b as h3c. auto. } } } Qed.


       
Lemma asks_of_perm (M M': list fill_type): perm M M' -> perm (asks_of M) (asks_of M').
Proof. { intro H. unfold perm in H. move /andP in H. destruct H.
         unfold perm. apply /andP. split. all: eapply included_M_imp_included_asks;exact. } Qed.

Lemma asks_of_nodup (F: list fill_type): NoDup (asks_of F) -> NoDup F.
Proof. { intro H. induction F. auto. assert (H1:NoDup (asks_of F)).
         simpl in H. eauto. apply IHF in H1 as H2. simpl in H. 
         assert (~In (ask_of a) (asks_of F)). eauto. 
         assert (~In a (F)). intro.  assert (H4:In (ask_of a) (asks_of F)).
         apply asks_of_elim0. exact. contradiction. eauto. } Qed.
 
Lemma asks_of_delete_delete (F: list fill_type) (m1 m2: fill_type):
  In m1 F -> In m2 F -> NoDup (asks_of F) -> 
(asks_of (delete m1 (delete m2 F))) = (delete (ask_of m1) (delete (ask_of m2) (asks_of F))).
Proof. { intros. assert (Hm1m2: m1=m2\/m1<>m2). eapply reflect_EM. auto.
       destruct Hm1m2.  
       { subst m1. simpl. assert (H2:(delete m2 (delete m2 F)) = delete m2 F).
         { assert (H3:~In m2 (delete m2 F) ). { apply delete_intro2. apply asks_of_nodup.
         exact. } apply delete_intro1 in H3. auto. } 
         assert (H3:(delete (ask_of m2) (delete (ask_of m2) (asks_of F))) = (delete (ask_of m2) (asks_of F))).
         { assert (H4:~In (ask_of m2) (delete (ask_of m2) (asks_of F))). { apply delete_intro2.  exact. } apply delete_intro1 in H4. auto. }
         rewrite H2. rewrite H3. apply asks_of_delete. exact. exact. }
       { assert (H3: (asks_of (delete m2 F)) = (delete (ask_of m2) (asks_of F))).
         apply asks_of_delete. exact. exact.
         assert (H4: (asks_of (delete m1 (delete m2 F))) = 
         (delete (ask_of m1) ((delete (ask_of m2) (asks_of F))))).
         rewrite <- H3. apply asks_of_delete. apply delete_intro. exact.  exact.   
         { assert (H4: (asks_of (delete m2 F)) = delete (ask_of m2) (asks_of F)).
           apply asks_of_delete. exact. exact. rewrite H4. eauto. } exact. }} Qed.


Fixpoint trade_prices_of (F: list fill_type) : (list nat) :=
  match F with
  |nil => nil
  |f::F'=> (tp f)::(trade_prices_of F')
  end.

Lemma trade_prices_of_intro (F: list fill_type) (m: fill_type):
  In m F -> In (tp m) (trade_prices_of F).
Proof. { intro H. induction F. eauto. destruct H. subst m.
       simpl. left;auto. simpl. right;auto.
       } Qed.

                           
Lemma trade_prices_of_elim (F: list fill_type): forall p, In p (trade_prices_of F) ->
                                                     exists m, In m F /\ p = tp m.
Proof. { intros p H. induction F. simpl in H. contradiction. simpl in H. destruct H.
       exists a. split. eauto. auto. apply IHF in H as H0. destruct  H0 as [m H0].
       destruct H0 as [H1 H2]. exists m. split;eauto. } Qed.
 
Lemma count_in_deleted_tp (m: fill_type)(M: list fill_type):
  In m M -> count (tp m)(trade_prices_of M) = S (count (tp m) (trade_prices_of (delete m M))).
  Proof.  { induction M.
       { simpl. auto. }
       { intro H1. destruct (m == a) eqn: H2.
         { simpl. rewrite H2. move /eqP in H2.
           subst a. simpl. replace (Nat.eqb (tp m) (tp m)) with true. auto. auto. }
         { assert (H1a: In m M).
           { move /eqP in H2. eapply element_list with (b:=m)(a:=a). auto. exact. }
           replace (delete m (a :: M)) with (a :: (delete m M)).
           { simpl. destruct (Nat.eqb (tp m) (tp a)) eqn: H3.
             { apply IHM in H1a as H1b. rewrite H1b. auto. }
             { auto. } }
           { simpl. rewrite H2. auto. } } } } Qed.

  
       
Lemma included_M_imp_included_tps (M M': list fill_type):
 included M M' -> included (trade_prices_of M) (trade_prices_of M').
 Proof. Proof. { revert M'. induction M as [| m].
       { simpl. auto. }
       { intros M' H1.
         assert (H2: In m M'). eauto.
         assert (H3: included M (delete m M')). eauto.
         assert (H3a: included (trade_prices_of M) (trade_prices_of (delete m M'))).
         { auto. }
         assert(H4:count (tp m)(trade_prices_of M')= S (count (tp m) (trade_prices_of (delete m M')))).
         { eauto using count_in_deleted_tp. }
         eapply included_intro.
         intro x.  simpl. destruct (Nat.eqb x (tp m)) eqn: C1.
         { (* ---- C1: x = b1 ---- *)
           move /nat_eqP in C1. subst x.
           rewrite H4.
           eapply included_elim in H3a  as H3b. instantiate (1 :=tp m) in H3b.
           lia. }
         { (*----- C1: x <> b1 ---- *)
           assert (H3b: included M M'). eapply included_elim4; apply H1. 
           apply IHM in H3b as H3c. auto. } } } Qed.

   
   
   
Lemma tps_of_perm (M M': list fill_type):
 perm M M' -> perm (trade_prices_of M) (trade_prices_of M').
Proof. { intro H. unfold perm in H. move /andP in H. destruct H.
         unfold perm. apply /andP. split. all: eapply included_M_imp_included_tps.
         exact. exact. } Qed.




      
Hint Resolve bids_of_intro bids_of_elim asks_of_intro asks_of_elim: core.
Hint Resolve trade_prices_of_intro trade_prices_of_elim: core.

Hint Resolve asks_of_intro1 bids_of_intro1 asks_of_perm bids_of_perm: core.
Hint Resolve bids_of_elim1 asks_of_elim1: core.


End BidAsk.


(*Definition b0 := {|bp:=0;idb:=0|}.
Definition a0 := {|sp:=0;ida:=0|}.
Definition m0 := {|bid_of:=b0;ask_of:=a0;tp:=0|}.*)

Hint Resolve b_eqb_ref b_eqP : core.
Hint Immediate b_eqb_elim b_eqb_intro: core.

Hint Resolve a_eqb_ref a_eqP : core.
Hint Immediate a_eqb_intro a_eqb_elim: core.


Hint Resolve bid_prices_elim bid_prices_intro bid_prices_intro1: core.
Hint Resolve ask_prices_elim ask_prices_intro ask_prices_intro1: core.


Hint Resolve m_eqb_ref m_eqP: core.
Hint Immediate m_eqb_elim m_eqb_intro: core.

      
Hint Resolve bids_of_intro bids_of_elim asks_of_intro asks_of_elim: core.
Hint Resolve trade_prices_of_intro trade_prices_of_elim: core.

Hint Resolve asks_of_intro1 bids_of_intro1 asks_of_perm bids_of_perm: core.

Hint Resolve bids_of_perm asks_of_perm tps_of_perm: core.
Hint Resolve bids_of_elim1 asks_of_elim1: core.
