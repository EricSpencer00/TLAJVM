---- MODULE TestProgram ----

EXTENDS Naturals, Sequences, TLC

VARIABLE pc
VARIABLE counter
VARIABLE isRunning

Init ==
  /\ pc = 0
  /\ counter = 0
  /\ isRunning = FALSE

Next ==
  \E Step0 ==
    /\ pc = 0
    /\ counter' = 0
    /\ pc' = 1
    /\ UNCHANGED <<isRunning>>
  \E Step1 ==
    /\ pc = 1
    /\ isRunning' = true
    /\ pc' = 2
    /\ UNCHANGED <<counter>>
  \E Step2 ==
    /\ pc = 2
    /\ isRunning
    /\ pc' = 3
    /\ UNCHANGED <<counter, isRunning>>
  \E Step3 ==
    /\ pc = 3
    /\ ~(isRunning)
    /\ pc' = 4
    /\ UNCHANGED <<counter, isRunning>>


Invariants ==
  /\ pc >= 0
  /\ counter \in Nat
  /\ isRunning \in BOOLEAN

TemporalProperties ==
  /\ WF_vars(pc)
  /\ WF_vars(counter)
  /\ WF_vars(isRunning)

DeadlockFreedom ==
  WF_vars(pc)

====