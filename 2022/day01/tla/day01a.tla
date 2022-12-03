------------------------------- MODULE day01a -------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT MaxElves, MaxItems, ItemValues
ASSUME /\ MaxElves \in Nat
       /\ MaxItems \in Nat
       /\ ItemValues \subseteq Nat
       
(*--fair algorithm spec {
    variables
        \* state sweeping
        numElves \in 0..MaxElves;
        numItems \in 0..MaxItems;
        input \in [1..numElves -> [1..numItems -> ItemValues]];
        \* real variables
        max = 0;
        calories = 0;
        elfIterator = 1;
        itemIterator = 1;
    
    define {
        TypeInvariant == /\ max \in Nat
                         /\ calories \in Nat
                         /\ elfIterator \in 1..MaxElves+1
                         /\ itemIterator \in 1..MaxItems+1
        
        VariableActionProps == /\ [][max <= max']_max
                               /\ [][calories' >= calories \/ calories' = 0]_calories
                               /\ [][elfIterator' = elfIterator + 1]_elfIterator
                               /\ [][itemIterator' = itemIterator + 1 \/ itemIterator' = 1]_itemIterator
                              
        Liveness == 
            LET
                SumSeq(s) ==
                    LET
                        RECURSIVE Helper(_)
                        Helper(s_) == IF s_ = <<>> THEN 0 ELSE Head(s_) + Helper(Tail(s_))
                    IN Helper(s)
                Max(S) == CHOOSE x \in S : \A y \in S : x >= y
            IN <>[]( max = IF input # <<>> THEN Max({ SumSeq(input[i]) : i \in DOMAIN input }) ELSE 0 )
    }
    
    {
        ElfLoop: while (elfIterator <= Len(input)) {
            NewElf:
                calories := 0;
                itemIterator := 1;
                
            ItemLoop: while (itemIterator <= Len(input[elfIterator])) {
                CountCalories: calories := calories + input[elfIterator][itemIterator];
                NextItem: itemIterator := itemIterator + 1;
            };
            
            UpdateMax: if (calories >= max) {
                max := calories
            };
            
            NextElf: elfIterator := elfIterator + 1;
        };
    }
}; *)
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "6ad58b8")
VARIABLES numElves, numItems, input, max, calories, elfIterator, itemIterator, 
          pc

(* define statement *)
TypeInvariant == /\ max \in Nat
                 /\ calories \in Nat
                 /\ elfIterator \in 1..MaxElves+1
                 /\ itemIterator \in 1..MaxItems+1

VariableActionProps == /\ [][max <= max']_max
                       /\ [][calories' >= calories \/ calories' = 0]_calories
                       /\ [][elfIterator' = elfIterator + 1]_elfIterator
                       /\ [][itemIterator' = itemIterator + 1 \/ itemIterator' = 1]_itemIterator

Liveness ==
    LET
        SumSeq(s) ==
            LET
                RECURSIVE Helper(_)
                Helper(s_) == IF s_ = <<>> THEN 0 ELSE Head(s_) + Helper(Tail(s_))
            IN Helper(s)
        Max(S) == CHOOSE x \in S : \A y \in S : x >= y
    IN <>[]( max = IF input # <<>> THEN Max({ SumSeq(input[i]) : i \in DOMAIN input }) ELSE 0 )


vars == << numElves, numItems, input, max, calories, elfIterator, 
           itemIterator, pc >>

Init == (* Global variables *)
        /\ numElves \in 0..MaxElves
        /\ numItems \in 0..MaxItems
        /\ input \in [1..numElves -> [1..numItems -> ItemValues]]
        /\ max = 0
        /\ calories = 0
        /\ elfIterator = 1
        /\ itemIterator = 1
        /\ pc = "ElfLoop"

ElfLoop == /\ pc = "ElfLoop"
           /\ IF elfIterator <= Len(input)
                 THEN /\ pc' = "NewElf"
                 ELSE /\ pc' = "Done"
           /\ UNCHANGED << numElves, numItems, input, max, calories, 
                           elfIterator, itemIterator >>

NewElf == /\ pc = "NewElf"
          /\ calories' = 0
          /\ itemIterator' = 1
          /\ pc' = "ItemLoop"
          /\ UNCHANGED << numElves, numItems, input, max, elfIterator >>

ItemLoop == /\ pc = "ItemLoop"
            /\ IF itemIterator <= Len(input[elfIterator])
                  THEN /\ pc' = "CountCalories"
                  ELSE /\ pc' = "UpdateMax"
            /\ UNCHANGED << numElves, numItems, input, max, calories, 
                            elfIterator, itemIterator >>

CountCalories == /\ pc = "CountCalories"
                 /\ calories' = calories + input[elfIterator][itemIterator]
                 /\ pc' = "NextItem"
                 /\ UNCHANGED << numElves, numItems, input, max, elfIterator, 
                                 itemIterator >>

NextItem == /\ pc = "NextItem"
            /\ itemIterator' = itemIterator + 1
            /\ pc' = "ItemLoop"
            /\ UNCHANGED << numElves, numItems, input, max, calories, 
                            elfIterator >>

UpdateMax == /\ pc = "UpdateMax"
             /\ IF calories >= max
                   THEN /\ max' = calories
                   ELSE /\ TRUE
                        /\ max' = max
             /\ pc' = "NextElf"
             /\ UNCHANGED << numElves, numItems, input, calories, elfIterator, 
                             itemIterator >>

NextElf == /\ pc = "NextElf"
           /\ elfIterator' = elfIterator + 1
           /\ pc' = "ElfLoop"
           /\ UNCHANGED << numElves, numItems, input, max, calories, 
                           itemIterator >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == ElfLoop \/ NewElf \/ ItemLoop \/ CountCalories \/ NextItem
           \/ UpdateMax \/ NextElf
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Fri Dec 02 14:41:21 PST 2022 by chris
\* Created Thu Dec 01 23:31:08 PST 2022 by chris
