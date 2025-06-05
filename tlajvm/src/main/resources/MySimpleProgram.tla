---- MODULE MySimpleProgram ----

VARIABLE pc
VARIABLE x
VARIABLE y

Init ==
  /\ pc = 0
  /\ x = 0
  /\ y = 0

Next ==
  \/ Step0 ==
     /\ pc = 0
     /\ x' = 10
     /\ pc' = 1
     /\ UNCHANGED y
  \/ Step1 ==
     /\ pc = 1
     /\ y' = x + 5
     /\ pc' = 2
     /\ UNCHANGED x
  \/ Step2 ==
     /\ pc = 2
     /\ IF y > 10
        THEN pc' = 3
        ELSE pc' = 4
     /\ UNCHANGED <<x, y>>

==== 