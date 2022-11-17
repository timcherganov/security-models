------------------------ MODULE HarrisonRuzzoUllman -------------------------
\* Harrison M., Ruzzo W., Ullman J. Protection in Operating Systems.
\* Communications of the ACM, August 1976, 19 (8): 461–471,
\* doi:10.1145/360303.360333.

CONSTANT R, \* rights
         E  \* entities

VARIABLES S, \* current subjects
          O, \* current objects
          P  \* access matrix

TypeOK == /\ O \subseteq E
          /\ S \subseteq O
          /\ P \in [S \times O -> SUBSET R]

-----------------------------------------------------------------------------
enterRight(r, s, o) == /\ P' = [P EXCEPT ![s, o] = P[s, o] \union {r}]
                       /\ UNCHANGED <<S, O>>

deleteRight(r, s, o) == /\ P' = [P EXCEPT ![s, o] = P[s, o] \ {r}]
                        /\ UNCHANGED <<S, O>>

createSubject(s) == /\ s \notin O
                    /\ S' = S \union {s}
                    /\ O' = O \union {s}
                    /\ P' = [x \in S' \times O' |-> IF x \in S \times O THEN P[x] ELSE {}]

createObject(o) == /\ o \notin O
                   /\ O' = O \union {o}
                   /\ P' = [x \in S \times O' |-> IF x \in S \times O THEN P[x] ELSE {}]
                   /\ UNCHANGED S

destroySubject(s) == /\ s \in S
                     /\ S' = S \ {s}
                     /\ O' = O \ {s}
                     /\ P' = [x \in S' \times O' |-> P[x]]

destroyObject(o) == /\ o \in O
                    /\ S' = S \ {o}
                    /\ O' = O \ {o}
                    /\ P' = [x \in S' \times O' |-> P[x]]

-----------------------------------------------------------------------------
Init == /\ O \in SUBSET E
        /\ S \in SUBSET O
        /\ P \in [S \times O -> SUBSET R]

Next == \/ \E r \in R, s \in S, o \in O : \/ enterRight(r, s, o)
                                          \/ deleteRight(r, s, o)
        \/ \E e \in E : \/ createSubject(e)
                        \/ createObject(e)
                        \/ destroySubject(e)
                        \/ destroyObject(e)

=============================================================================
\* Modification History
\* Last modified Thu Nov 17 14:42:10 MSK 2022 by tim
\* Created Wed Nov 16 10:09:26 MSK 2022 by tim
