#Introduction.

This folder contains the coq formalization of double-sided auctions with multiplicity (dsam). 
DSA is used in the financial markets by exchanges for trading between multiple buyers with multiple sellers. 
For example,  double-sided auction with multiplicity is used during the call auction session of trading at a stock exchange. 
In this formalization, we have modeled and formalized various properties of double sided auction along with their algorithms. 
We extract a certified OCaml, Haskell programs for matching buyers with seller at the stock exchange during call auction session.
We also have demonstrated our extracted OCaml programs on real market data. Please see directory Demonstration.

#How to use the coq formalization: To compile the code please run the executable shell script auction.sh

# Coq files details: We have formalized matching at the financial exchanges. 
0. All the important results, processes and programs are extracted in Demo.v file. To run this file, please 
run auction.sh file from you terminal ($ ./auction.sh). This file may take 5-6 minutes to compile. 
Once auctions.sh is successfully completed, please run "coqc Demo.v" from your terminal. In short, 
type the following command from your terminal:

> ./auction.sh;
> coqc Demo.v 

1. The main lemmas for the correctness of fairness are in the file MQFAIR.v
2. The UM process and its correctness theorems are in MQUM.v. The UM process is used at the exchanges.
3. For MM process, go to the file MQMM.v.
4. The Bound.v file contains combinatorial results on matchings. 
5. The Uniqueness.v file contains uniqueness related results.

Following are some of the important observations about some of the pre-conditions.

Note1: It is natural to believe that the bids and asks comes with 
non-zero quantity. It is easy to ensure that all the zero quantity bids
or zero quantity asks are removed from the system on arrival.
These assertions below are denoted as 'NZB' and 'NZA' respectively.

Note2: Since no bid or asks is of non-zero quantity a matching can be
assumed to have non-zero transactions. This assertion is represented as
'NZT'.

Note3: Each bid or ask is assigned a unique time stamp and unique id 
on arrival. So it is easy to see that we do not have two bids or asks with 
same ids in the lists B and A. These assertions are denoted as 'NDA' and 'NDB'.

Note4: (Similar to Note3) since a bid or ask has a unique time-stamp, we have two natural hypothesis that not two different orders for same securities should be 
assigned same time-stamp. This is natural, otherwise it is difficult to break the tie for the competitiveness in the markets.
