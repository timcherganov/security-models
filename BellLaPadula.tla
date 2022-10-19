---------------------------- MODULE BellLaPadula ----------------------------
\* David Bell and Leonard LaPadula. Secure computer system: Uniﬁed exposition
\* and Multics implementation. Technical Report ESD-TR-75-306, The MITRE
\* Corporation, Bedford, MA, July 1975.

CONSTANTS S,   \* subjects: processes, programs in execution
          O,   \* objects: data, files, programs, subjects, I/0 devices
          L,   \* security levels
          _<=_ \* partial order relation on L

VARIABLES b,   \* current access of subjects to objects
          m,   \* access matrice
          f    \* security level vector:
               \* - f.s : the maximal security level each subject can have
               \* - f.o : the object security level
               \* - f.c : the current security level of each subject

IsPartialOrder(R(_,_), X) ==
  /\ \A x \in X : R(x, x)                              \* reflexive
  /\ \A x, y \in X : R(x, y) /\ R(y, x) => x = y       \* antisymmetric
  /\ \A x, y, z \in X : R(x, y) /\ R(y, z) => R(x, z)  \* transitive
  
ASSUME IsPartialOrder(<=, L)

\* Access attributes:
\* - r: read-only;
\* - e: execute (no read, no write);
\* - w: write (read and write);
\* - a: append (write-only).
A == {"r", "e", "w", "a"}

B == SUBSET [s : S, o : O, a : A]

M == [S \times O -> SUBSET A]

\* The set of security level vectors. The current level of a subject cannot
\* be higher than its maximal level.
F == { g \in [s : [S -> L], o : [O -> L], c : [S -> L]] : \A x \in S : g.c[x] <= g.s[x] }

TypeOK ==/\ b \in B
         /\ m \in M 
         /\ f \in F

-----------------------------------------------------------------------------
\* Security propertiers

NoReadUp(x, g) == x.a \in {"r", "w"} => g.o[x.o] <= g.s[x.s]

NoWriteDown(x, g) == /\ x.a = "r" => g.o[x.o] <= g.c[x.s]
                     /\ x.a = "w" => g.c[x.s] = g.o[x.o] 
                     /\ x.a = "a" => g.c[x.s] <= g.o[x.o]

\* The simple security property
SS == \A x \in b : NoReadUp(x, f)

\* The *-property
Star == \A x \in b : NoWriteDown(x, f)

\* The discretionary security property
DS == \A x \in b : x.a \in m[x.s, x.o]

\* A state is called secure if it satisfies the simple security property,
\* the *-property, and the discretionary security property.
Secure == SS /\ Star /\ DS

-----------------------------------------------------------------------------
\* Security preservation

PreserveSS == /\ \A x \in (b' \ b) : NoReadUp(x, f')
              /\ \A x \in b : ~ NoReadUp(x, f') => x \notin b'

PreserveStar == /\ \A x \in (b' \ b) : NoWriteDown(x, f')
                /\ \A x \in b : ~ NoWriteDown(x, f') => x \notin b'

PreserveDS == /\ \A x \in (b' \ b) : x.a \in m'[x.s, x.o]
              /\ \A x \in b : x.a \notin m'[x.s, x.o] => x \notin b'

Preserve == PreserveSS /\ PreserveStar /\ PreserveDS

-----------------------------------------------------------------------------
Init == TypeOK /\ Secure

Next == /\ b' \in B
        /\ m' \in M
        /\ f' \in F
        /\ Preserve

=============================================================================
\* Modification History
\* Last modified Wed Oct 19 15:14:19 MSK 2022 by tim
\* Created Wed Oct 12 08:01:40 MSK 2022 by tim
