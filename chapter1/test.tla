-------------------------------- MODULE test --------------------------------

EXTENDS Integers,TLC,FiniteSets
(*--algorithm test
variables
    x \in 1..2,
    y = SUBSET { "a", "b", "c", "a" };
begin
    assert Cardinality(y) = 8;
    assert x <= 2;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "6094a9d4" /\ chksum(tla) = "4b15f59d")
VARIABLES x, y, pc

vars == << x, y, pc >>

Init == (* Global variables *)
        /\ x \in 1..2
        /\ y = SUBSET { "a", "b", "c", "a" }
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(Cardinality(y) = 8, 
                   "Failure of assertion at line 9, column 5.")
         /\ Assert(x <= 2, "Failure of assertion at line 10, column 5.")
         /\ pc' = "Done"
         /\ UNCHANGED << x, y >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Sat Oct 16 20:08:40 JST 2021 by yoshitsugu
\* Created Mon Oct 11 21:28:50 JST 2021 by yoshitsugu
