---- MODULE ComplexExample ----

EXTENDS Naturals, Sequences, TLC

VARIABLE pc
VARIABLE numbers
VARIABLE flags
VARIABLE sum
VARIABLE isProcessing

Init ==
  /\ pc = 0
  /\ numbers = 0
  /\ flags = FALSE
  /\ sum = 0
  /\ isProcessing = FALSE

Next ==
  \E Step0 ==
    /\ pc = 0
    /\ isProcessing
    /\ pc' = 1
    /\ UNCHANGED <<numbers, flags, sum, isProcessing>>
  \E Step1 ==
    /\ pc = 1
    /\ ~(isProcessing)
    /\ pc' = 2
    /\ UNCHANGED <<numbers, flags, sum, isProcessing>>
  \E Step2 ==
    /\ pc = 2
    /\ sum' = sum + value
    /\ pc' = 3
    /\ UNCHANGED <<numbers, flags, isProcessing>>
  \E Step3 ==
    /\ pc = 3
    /\ boolean result' = true
    /\ pc' = 4
    /\ UNCHANGED <<numbers, flags, sum, isProcessing>>
  \E Step4 ==
    /\ pc = 4
    /\ j < flags[row].length
    /\ pc' = 5
    /\ UNCHANGED <<numbers, flags, sum, isProcessing, boolean result>>
  \E Step5 ==
    /\ pc = 5
    /\ ~(j < flags[row].length)
    /\ pc' = 6
    /\ UNCHANGED <<numbers, flags, sum, isProcessing, boolean result>>
  \E Step6 ==
    /\ pc = 6
    /\ ComplexExample example' = new ComplexExample()
    /\ pc' = 7
    /\ UNCHANGED <<numbers, flags, sum, isProcessing, boolean result>>


Invariants ==
  /\ pc >= 0
  /\ numbers \in Nat
  /\ flags \in BOOLEAN
  /\ sum \in Nat
  /\ isProcessing \in BOOLEAN
  /\ boolean result \in BOOLEAN
  /\ ComplexExample example \in Nat

TemporalProperties ==
  /\ WF_vars(pc)
  /\ WF_vars(numbers)
  /\ WF_vars(flags)
  /\ WF_vars(sum)
  /\ WF_vars(isProcessing)
  /\ WF_vars(boolean result)
  /\ WF_vars(ComplexExample example)

DeadlockFreedom ==
  WF_vars(pc)

====