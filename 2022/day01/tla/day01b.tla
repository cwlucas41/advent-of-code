------------------------------- MODULE day01b -------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT MaxElves, MaxItems, ItemValues, MaxTopN
ASSUME /\ MaxElves \in Nat
       /\ MaxItems \in Nat
       /\ ItemValues \subseteq Nat
       /\ MaxTopN \in Nat /\ MaxTopN <= MaxElves
       
SumSeq(s) ==
    LET
        RECURSIVE Helper(_)
        Helper(s_) == IF s_ = <<>> THEN 0 ELSE Head(s_) + Helper(Tail(s_))
    IN Helper(s)
       
(*--fair algorithm spec {
    variables
        \* state sweeping
        numElves \in 0..MaxElves;
        numItems \in 0..MaxItems;
        \* correct for cases in sweeping where MaxTopN > numElves in state by using mininum of two
        topN \in 0..(LET S == {MaxTopN, numElves} IN CHOOSE x \in S : \A y \in S : x <= y);
        input \in [1..numElves -> [1..numItems -> ItemValues]];
        \* real variables
        max = 0;
        elfIterator = 1;
        itemIterator = 1;
        maxIterator = 1;
        calories = 0;
        maxes = <<>>;
        minIndex = 1;
    
    define {
        TypeInvariant == /\ max \in Nat
                         /\ elfIterator \in 1..MaxElves+1
                         /\ itemIterator \in 1..MaxItems+1
                         /\ maxIterator \in 1..topN+1
                         /\ calories \in Nat
                         /\ maxes \in Seq(Nat) /\ DOMAIN(maxes) \subseteq 1..topN
                         /\ minIndex \in 1..topN+1
        
        VariableActionProps == /\ [][max' > max]_max
                               /\ [][calories' >= calories \/ calories' = 0]_calories
                               /\ [][Len(maxes') >= Len(maxes)]_maxes
                               /\ [][ \A maxIndex \in DOMAIN(maxes) : maxes[maxIndex]' >= maxes[maxIndex]]_maxes
                              
        Liveness == 
            LET
                elfTotals == [i \in DOMAIN(input) |-> SumSeq(input[i])]
                topNElfTotals == SubSeq(SortSeq(elfTotals, \geq), 1, topN)
                total == SumSeq(topNElfTotals)
            IN <>[]( max = IF input # <<>> THEN total ELSE 0 )
    }
    
    {
        ElfLoop: while (elfIterator <= Len(input)) {
        
            calories := 0;
            itemIterator := 1;
            
            ItemLoop: while (itemIterator <= Len(input[elfIterator])) {
                calories := calories + input[elfIterator][itemIterator];
                itemIterator := itemIterator + 1;
            };
            
            if (Len(maxes) < topN) {
                NewMax: maxes := Append(maxes, calories)
            } else {
                maxIterator := 1;
                minIndex := 1;
                FindMinMax: while (maxIterator <= Len(maxes)) {
                    if (maxes[maxIterator] < maxes[minIndex]) {
                        minIndex := maxIterator;
                    };
                    
                    maxIterator := maxIterator + 1;
                };
                
                if (maxes # <<>> /\ maxes[minIndex] < calories) {
                    maxes[minIndex] := calories;
                }
            };
            
            NextElf: elfIterator := elfIterator + 1;
        };
        
        maxIterator := 1;
        ComputeSum: while(maxIterator <= Len(maxes)) {
            max := max + maxes[maxIterator];
            maxIterator := maxIterator + 1;
        }
    }
}; *)
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "25e3ca00")
VARIABLES numElves, numItems, topN, input, max, elfIterator, itemIterator, 
          maxIterator, calories, maxes, minIndex, pc

(* define statement *)
TypeInvariant == /\ max \in Nat
                 /\ elfIterator \in 1..MaxElves+1
                 /\ itemIterator \in 1..MaxItems+1
                 /\ maxIterator \in 1..topN+1
                 /\ calories \in Nat
                 /\ maxes \in Seq(Nat) /\ DOMAIN(maxes) \subseteq 1..topN
                 /\ minIndex \in 1..topN+1

VariableActionProps == /\ [][max' > max]_max
                       /\ [][calories' >= calories \/ calories' = 0]_calories
                       /\ [][Len(maxes') >= Len(maxes)]_maxes
                       /\ [][ \A maxIndex \in DOMAIN(maxes) : maxes[maxIndex]' >= maxes[maxIndex]]_maxes

Liveness ==
    LET
        elfTotals == [i \in DOMAIN(input) |-> SumSeq(input[i])]
        topNElfTotals == SubSeq(SortSeq(elfTotals, \geq), 1, topN)
        total == SumSeq(topNElfTotals)
    IN <>[]( max = IF input # <<>> THEN total ELSE 0 )


vars == << numElves, numItems, topN, input, max, elfIterator, itemIterator, 
           maxIterator, calories, maxes, minIndex, pc >>

Init == (* Global variables *)
        /\ numElves \in 0..MaxElves
        /\ numItems \in 0..MaxItems
        /\ topN \in 0..(LET S == {MaxTopN, numElves} IN CHOOSE x \in S : \A y \in S : x <= y)
        /\ input \in [1..numElves -> [1..numItems -> ItemValues]]
        /\ max = 0
        /\ elfIterator = 1
        /\ itemIterator = 1
        /\ maxIterator = 1
        /\ calories = 0
        /\ maxes = <<>>
        /\ minIndex = 1
        /\ pc = "ElfLoop"

ElfLoop == /\ pc = "ElfLoop"
           /\ IF elfIterator <= Len(input)
                 THEN /\ calories' = 0
                      /\ itemIterator' = 1
                      /\ pc' = "ItemLoop"
                      /\ UNCHANGED maxIterator
                 ELSE /\ maxIterator' = 1
                      /\ pc' = "ComputeSum"
                      /\ UNCHANGED << itemIterator, calories >>
           /\ UNCHANGED << numElves, numItems, topN, input, max, elfIterator, 
                           maxes, minIndex >>

ItemLoop == /\ pc = "ItemLoop"
            /\ IF itemIterator <= Len(input[elfIterator])
                  THEN /\ calories' = calories + input[elfIterator][itemIterator]
                       /\ itemIterator' = itemIterator + 1
                       /\ pc' = "ItemLoop"
                       /\ UNCHANGED << maxIterator, minIndex >>
                  ELSE /\ IF Len(maxes) < topN
                             THEN /\ pc' = "NewMax"
                                  /\ UNCHANGED << maxIterator, minIndex >>
                             ELSE /\ maxIterator' = 1
                                  /\ minIndex' = 1
                                  /\ pc' = "FindMinMax"
                       /\ UNCHANGED << itemIterator, calories >>
            /\ UNCHANGED << numElves, numItems, topN, input, max, elfIterator, 
                            maxes >>

NewMax == /\ pc = "NewMax"
          /\ maxes' = Append(maxes, calories)
          /\ pc' = "NextElf"
          /\ UNCHANGED << numElves, numItems, topN, input, max, elfIterator, 
                          itemIterator, maxIterator, calories, minIndex >>

FindMinMax == /\ pc = "FindMinMax"
              /\ IF maxIterator <= Len(maxes)
                    THEN /\ IF maxes[maxIterator] < maxes[minIndex]
                               THEN /\ minIndex' = maxIterator
                               ELSE /\ TRUE
                                    /\ UNCHANGED minIndex
                         /\ maxIterator' = maxIterator + 1
                         /\ pc' = "FindMinMax"
                         /\ maxes' = maxes
                    ELSE /\ IF maxes # <<>> /\ maxes[minIndex] < calories
                               THEN /\ maxes' = [maxes EXCEPT ![minIndex] = calories]
                               ELSE /\ TRUE
                                    /\ maxes' = maxes
                         /\ pc' = "NextElf"
                         /\ UNCHANGED << maxIterator, minIndex >>
              /\ UNCHANGED << numElves, numItems, topN, input, max, 
                              elfIterator, itemIterator, calories >>

NextElf == /\ pc = "NextElf"
           /\ elfIterator' = elfIterator + 1
           /\ pc' = "ElfLoop"
           /\ UNCHANGED << numElves, numItems, topN, input, max, itemIterator, 
                           maxIterator, calories, maxes, minIndex >>

ComputeSum == /\ pc = "ComputeSum"
              /\ IF maxIterator <= Len(maxes)
                    THEN /\ max' = max + maxes[maxIterator]
                         /\ maxIterator' = maxIterator + 1
                         /\ pc' = "ComputeSum"
                    ELSE /\ pc' = "Done"
                         /\ UNCHANGED << max, maxIterator >>
              /\ UNCHANGED << numElves, numItems, topN, input, elfIterator, 
                              itemIterator, calories, maxes, minIndex >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == ElfLoop \/ ItemLoop \/ NewMax \/ FindMinMax \/ NextElf
           \/ ComputeSum
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Sat Dec 03 00:04:25 PST 2022 by chris
\* Created Thu Dec 01 23:31:08 PST 2022 by chris
