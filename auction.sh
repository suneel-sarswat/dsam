#!/bin/bash


printf "Compiling Basic list libraries.\n"
coqc GenReflect.v

coqc SetSpecs.v

coqc MinMax.v

coqc DecSort.v

coqc DecType.v

coqc SetReflect.v

coqc DecList.v

coqc MoreDecList.v

printf "Compiling auction libraries.\n"
coqc mBidAsk.v

coqc Quantity.v

coqc mMatching.v

printf "Compiling Fair on Bid: this may take some time.\n"
coqc mFair_Bid.v

printf "Compiling Fair on Ask: this may take some time.\n"
coqc mFair_Ask.v

printf "Compiling Fair: this takes a few minutes.\n"
coqc MQFair.v

printf "Compiling UM: this takes a few minutes.\n"
coqc MatchingAlter.v

coqc mUM.v

coqc MQUM.v


printf "Compiling MM: this takes a few minutes.\n"
coqc mMM.v

coqc MQMM.v

printf "Compiling Bounds and Uniqueness.\n"
coqc Bound.v

coqc Uniqueness.v

printf "Extracting codes into Demonstration directory. See Demo.v file for more details .\n"

coqc Demo.v


printf "Completed compiling all the files!"
echo \



