------------------------------- MODULE trash -------------------------------

EXTENDS Sequences, Integers, TLC
(*--algorithm trash
variables
    capacity \in [trash: 1..10, recycle: 1..10],
    bins = [trash |-> <<>>, recycle |-> <<>>],
    count = [trash |-> 0, recycle |-> 0],
    items \in SetsOfTwo(Items),
    curr = "";

define
    BinTypes == {"trash", "recycle"}
    SetsOf(set, c) == [1..c -> set]
    SetsOfTwo(set) == SetsOf(set, 3)
    Items == [type: BinTypes, size: 1..6]
    Invariant ==
        /\ capacity.trash >= 0
        /\ capacity.recycle >= 0
        /\ Len(bins.trash) >= count.trash
        /\ Len(bins.recycle) >= count.recycle
    AllLessThan(set, max) == \A num \in set: num < max
    IsCommutativeOver(Op(_, _), S)
      == \A x, y \in S: Op(x, y) = Op(y, x)
end define;

macro add_item(type) begin
    bins[type] := Append(bins[type], curr);
    capacity[type] := capacity[type] - curr.size;
    count[type] := count[type] + 1;
end macro

begin
    while items /= <<>> do
        curr := Head(items);
        items := Tail(items);
        if curr.type = "recycle"
                /\ curr.size < capacity.recycle then
            add_item("recycle");
        elsif curr.size < capacity.trash then
            add_item("trash");
        end if;
    end while;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "ddc70b9b" /\ chksum(tla) = "c0cd30be")
VARIABLES capacity, bins, count, items, curr, pc

(* define statement *)
BinTypes == {"trash", "recycle"}
SetsOf(set, c) == [1..c -> set]
SetsOfTwo(set) == SetsOf(set, 3)
Items == [type: BinTypes, size: 1..6]
Invariant ==
    /\ capacity.trash >= 0
    /\ capacity.recycle >= 0
    /\ Len(bins.trash) >= count.trash
    /\ Len(bins.recycle) >= count.recycle
AllLessThan(set, max) == \A num \in set: num < max
IsCommutativeOver(Op(_, _), S)
  == \A x, y \in S: Op(x, y) = Op(y, x)


vars == << capacity, bins, count, items, curr, pc >>

Init == (* Global variables *)
        /\ capacity \in [trash: 1..10, recycle: 1..10]
        /\ bins = [trash |-> <<>>, recycle |-> <<>>]
        /\ count = [trash |-> 0, recycle |-> 0]
        /\ items \in SetsOfTwo(Items)
        /\ curr = ""
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF items /= <<>>
               THEN /\ curr' = Head(items)
                    /\ items' = Tail(items)
                    /\ IF curr'.type = "recycle"
                                /\ curr'.size < capacity.recycle
                          THEN /\ bins' = [bins EXCEPT !["recycle"] = Append(bins["recycle"], curr')]
                               /\ capacity' = [capacity EXCEPT !["recycle"] = capacity["recycle"] - curr'.size]
                               /\ count' = [count EXCEPT !["recycle"] = count["recycle"] + 1]
                          ELSE /\ IF curr'.size < capacity.trash
                                     THEN /\ bins' = [bins EXCEPT !["trash"] = Append(bins["trash"], curr')]
                                          /\ capacity' = [capacity EXCEPT !["trash"] = capacity["trash"] - curr'.size]
                                          /\ count' = [count EXCEPT !["trash"] = count["trash"] + 1]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED << capacity, bins, 
                                                          count >>
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << capacity, bins, count, items, curr >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Sun Oct 17 20:29:14 JST 2021 by yoshitsugu
\* Created Sat Oct 16 20:25:30 JST 2021 by yoshitsugu
