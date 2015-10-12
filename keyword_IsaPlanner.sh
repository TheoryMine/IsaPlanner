#!/bin/sh
# This script file generates the keyword file '.el'
# used to extend Isabelle/HOL/Isar commands with 
# Isabelle/HOL/Isar/IsaPlanner commands.


ACTUAL_D_T="$(pwd)"
ISABELLE_LOGS_T="$(isabelle getenv -b ISABELLE_OUTPUT)"/log
ISABELLE_HOME_T="$(isabelle getenv -b ISABELLE_HOME)"
ML_IDENTIFIER_T="$(isabelle getenv -b ML_IDENTIFIER)"

cd $ISABELLE_HOME_T
./build -b -m "Pure"
./build -b -m "HOL"
./build -b -m "Pure-ProofGeneral" "Pure"

cp heaps/$ML_IDENTIFIER_T/log/Pure.gz $ISABELLE_LOGS_T
cp heaps/$ML_IDENTIFIER_T/log/HOL.gz $ISABELLE_LOGS_T
cp heaps/$ML_IDENTIFIER_T/log/Pure-ProofGeneral.gz $ISABELLE_LOGS_T

cd $ACTUAL_D_T
isabelle make clean
isabelle make

isabelle keywords -k HOL_IsaP $ISABELLE_LOGS_T/{Pure.gz,HOL.gz,Pure-ProofGeneral.gz,HOL_IsaP.gz}