Require Export MQFair.
Require Export MQUM.
Require Export MQMM.
Require Export Bound.
(*This is a demo file and it contains results from our paper titled
"Verified Double Sided Auctions in Financial Markets". This file contains
three important processes and their main theorems of corrctness. Besides we also have a combinatorial property.
Here is semantics of term.
1. matching_in M B A : 
M is a matching in the list of bids B and list of asks A.
2a. QM(M) : measures the total volume of a matching M.
2b. QB(B) : measures the total volume of bids of B.
2c. QA(A) : measures the total volume of asks of A.
3. NDB is assertations that bids are duplicate-free. Similarly, NDA.
4. NZT, NZA and NZB are assertations that quantity of a transaction, ask and
 bid is non-zero, respectively.
5. Hanti is for the anti-symmetric property of Bids and Asks.
6a. sort by_dbp : order the lists of bids by their competativeness.
6b. sort by_sp :  order the lists of asks by their competativeness.
6c. sort by_dsp : increasing order the lists of asks by their competativeness.
( simlialrly, list of matching is also sorted by bids present in the matching
 and asks present in the matching. The term m_sp and m_dsp is used.
7. Is_uniform M B A: M is a matching which is uniform and IR.
8. 
*)

(*############### 1. FAIR  #######################*)

(*This is FAIR process. The FAIR process takes a matching M and a lis of duplicate-free Bids B and a list of duplicate-free Asks A as inputs. 
It outputs a fair matching on the same list of bids and asks (B and A) 
without compromizing on the total volume of M. A direct cosequence of this
 result is that there always exists a maximum matching which is also fair.*)

Definition fair_on_asks (M: list fill_type) (A: list Ask):=
  (forall s s', In s A /\ In s' A -> s < s' -> In s' (asks_of M) ->
  (ttqa M s')>0 -> 
  (In s (asks_of M)/\(ttqa M s= sq s))).

Definition fair_on_bids (M: list fill_type)(B: list Bid):=
  (forall b b', In b B /\ In b' B -> b > b' -> In b' (bids_of M) -> 
  (ttqb M b')>0-> 
  (In b (bids_of M)/\(ttqb M b= bq b))).
 

Definition Is_fair (M: list fill_type) (B: list Bid) (A: list Ask) 
  :=  fair_on_asks M A /\ fair_on_bids M B.

Definition FAIR (M: list fill_type) (B: list Bid) (A: list Ask) :=
FOB (sort m_dbp (FOA (sort m_sp M) (sort by_sp A))) (sort by_dbp B).


Theorem FAIR_main (M: list fill_type)(B: list Bid)(A:list Ask)
(NDB: NoDup B) (NDA: NoDup A)(NZT:(forall m, In m M -> (tq m) > 0))
(NZA:(forall a0, In a0 A -> (sq a0) > 0))
(Hanti: (antisymmetric by_sp)/\(antisymmetric by_dbp) ): 
matching_in B A M-> 
(matching_in B A (FAIR M B A))/\
(Is_fair (FAIR M B A) B A)/\
(QM(M)= QM((FAIR M B A))).
Proof. apply FAIR_correct. all: auto. Qed.

(*############### 2. UM  #######################*)

(*This is UM process. The UM process takes a list of duplicate-free Bids B and a list of duplicate-free Asks A as inputs. 
It outputs a matching on the same list of bids and asks (B and A). The output
of UM is fair, uniform, IR and maximum amongst all the uniform matchings.
This process is used by the financial exchanges (stock, commodities etc. )
to match buyers and sellers.*)


Definition UM B A:=  
replace_column 
(UM_aux (sort by_dbp B) (sort by_sp A) 0 0) 
(uniform_price (sort by_dbp B) (sort by_sp A)).


Theorem UM_main (B:list Bid)(A:list Ask)(M:list fill_type)
(NZT: forall m : fill_type, In m M -> tq m > 0)
(NZB: forall b, In b B -> (bq b)>0)
(NZA: forall a, In a A -> (sq a)>0)
(NDA:NoDup (idas_of A))
(NDB:NoDup (idbs_of B))
(Hanti: (antisymmetric by_sp)/\(antisymmetric by_dbp)):
Is_uniform M B A ->
(Is_uniform (UM B A) B A)/\  (*UM is uniform and IR*)
(Is_fair (UM B A) B A)/\     (*UM is fair *)
(QM((UM B A))>=QM(M)).       (*UM is maximum amongs all uniform and IR*)
Proof. intro. split. apply UM_Is_Uniform. all: auto. 
       split. apply UM_FAIR. all: auto. apply UM_Maximum. all:auto. Qed.


(*############### 3. MM  #######################*)

(*This is MM process. The MM process takes a list of duplicate-free Bids B and a list of duplicate-free Asks A as inputs. 
It outputs a matching on the same list of bids and asks (B and A). The output
of MM is fair, IR and maximum amongst all the matchings on B and A.
*)


Definition MM B A:=  
(MM_aux (sort by_dbp B) (sort by_dsp A) 0 0).


Theorem MM_main (B:list Bid)(A:list Ask)(M:list fill_type)
(NZB: forall b, In b B -> (bq b)>0)
(NZA: forall a, In a A -> (sq a)>0)
(NDA:NoDup (idas_of A))
(NDB:NoDup (idbs_of B))
(NZT: forall m : fill_type, In m M -> tq m > 0)
(Hanti: (antisymmetric by_dsp)/\(antisymmetric by_dbp)):
Sorted by_dbp B ->
Sorted by_dsp A ->
matching_in B A M /\ Is_IR M->
(matching_in B A (MM B A))/\(Is_IR (MM B A))/\(QM((MM B A))>=QM(M)).
Proof. intros. split. apply MM_Is_IR_Matching. all:auto.
               split. apply MM_Is_IR_Matching. all:auto.
               apply MM_Maximum. all:auto. Qed.


(*A maximum fair matching can be obtained by applying the FAIR function of the 
output of MM. And the proof follows from FAIR_main *)

Definition MM_FAIR B A := FAIR (MM B A) B A.               

Theorem MM_fair (B:list Bid)(A:list Ask)(M:list fill_type)
(NZB: forall b, In b B -> (bq b)>0)
(NZA: forall a, In a A -> (sq a)>0)
(NDA:NoDup (idas_of A))
(NDB:NoDup (idbs_of B))
(Hnti: (antisymmetric by_dsp)/\(antisymmetric by_dbp)/\(antisymmetric by_sp )):
Is_fair (MM_FAIR B A) B A.
Proof. apply MM_FAIR_correct. all:auto. Qed. 

(*############### 4. Combinatorial results #######################*)

(*Below we have main combinatorial result from the paper.

The term (buyers_above p B) reprents bids of B with limit price more than or
 equal to  p. Similarly, (sellers_below p A) represents asks of A with limit
  price less than or equal to p. Hence QB(buyers_above p B) and QA(sellers_below p A) is total demand and supply at price p, respectively. *)


Theorem bound
(M: list fill_type) (B:list Bid) (A:list Ask) (p:nat)
(NDB: NoDup B)(NDA: NoDup A):
(matching_in B A M) -> 
QM(M)<= QB(buyers_above p B) + QA(sellers_below p A).
Proof. apply bound_on_M. all:auto. Qed.


(*Note: For all other intermediate results please look at respective files*)



(*################ Extracted Programs ############################*)
(*Now we extract programs from the above process*)

Require Extraction.
Extraction  Language Haskell.
Recursive Extraction FAIR.
Recursive Extraction UM.
Recursive Extraction MM_FAIR.

Extraction  Language OCaml.
Recursive Extraction FAIR.
Recursive Extraction UM.
Recursive Extraction MM_FAIR.
