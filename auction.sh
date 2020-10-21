#!/bin/bash


printf ‘GenReflect
coqc GenReflect.v

printf ‘SetSpecs.v
coqc SetSpecs.v

printf ‘DecSort.v
coqc DecSort.v

printf ‘MinMax.v
coqc MinMax.v

printf ‘DecType.v
coqc DecType.v

printf ‘SetReflect.v
coqc SetReflect.v

printf ‘DecList.v
coqc DecList.v

printf ‘MoreDecList.v
coqc MoreDecList.v

printf ‘mBidAsk.v
coqc mBidAsk.v

printf ‘Quantity.v
coqc Quantity.v

printf ‘MQMatching.v
coqc mMatching.v

printf ‘Fair_bids.v
coqc mFair_Bid.v

printf ‘Fair_asks.v
coqc mFair_Ask.v

printf ‘Fair.v
coqc MQFair.v

coqc MatchingAlter.v

printf ‘UM
coqc mUM.v

coqc MQUM.v

echo \



