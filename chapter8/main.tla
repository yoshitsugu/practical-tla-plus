-------------------------------- MODULE main --------------------------------
EXTENDS TLC, Integers, FiniteSets, Sequences

CONSTANTS Nodes, NULL
INSTANCE LinkedLists WITH NULL <- NULL
AllLinkedLists == LinkedLists(Nodes)


CycleImpliesTwoParents(ll) ==
    Cyclic(ll) <=> 
        \/ Ring(ll)
        \/ \E n \in DOMAIN ll:
            Cardinality({p \in DOMAIN ll: ll[p] = n}) = 2

CoveringRing(ll, nodes) ==
    /\ \E l \in ll:
        /\ Ring(l)
        /\ nodes \subseteq Range(l) 

Valid ==
    /\ \A ll \in AllLinkedLists:
        /\ Assert(CycleImpliesTwoParents(ll), <<"Counterexample:", ll>>)
    /\ \E ll \in AllLinkedLists:
        /\ Assert(Cyclic(ll), TRUE)
    /\ \E ll \in AllLinkedLists:
        /\ Assert(Cyclic(ll), FALSE)
    /\ \A subnodes \in SUBSET(Nodes) \ {{}}:
        /\ Assert(CoveringRing(AllLinkedLists, subnodes), TRUE)
        
=============================================================================
\* Modification History
\* Last modified Fri Nov 12 21:03:52 JST 2021 by yoshitsugu
\* Created Tue Nov 09 05:24:42 JST 2021 by yoshitsugu
