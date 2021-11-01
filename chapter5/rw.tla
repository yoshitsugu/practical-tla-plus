-------------------------------- MODULE rw -------------------------------

EXTENDS TLC, Integers, Sequences
CONSTANTS MaxQueueSize

(*--algorithm message_quieue

variable queue = <<>>;

define
      BoundedQueue == Len(queue) <= MaxQueueSize
end define;

procedure add_to_queue(val="") begin
    Add:
        await Len(queue) < MaxQueueSize;
        queue := Append(queue, val);
        return;
end procedure;

process writer = "writer"
begin Write:
    while TRUE do
        add_to_queue("msg");
        \* queue := Append(queue, "msg");
        \* await Len(queue) <= MaxQueueSize;
    end while;
end process;

process reader \in { "r1", "r2" }
variables current_message = "none";
begin Read:
    while TRUE do
        await queue /= <<>>;
        current_message := Head(queue);
        queue := Tail(queue);
        either
            skip;
        or
            NotifyFailure:
                current_message := "none";
                call add_to_queue(self);
        end either;
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "5f86ed68" /\ chksum(tla) = "78a5c1e4")
VARIABLES queue, pc

(* define statement *)
BoundedQueue == Len(queue) <= MaxQueueSize

VARIABLE current_message

vars == << queue, pc, current_message >>

ProcSet == {"writer"} \cup ({ "r1", "r2" })

Init == (* Global variables *)
        /\ queue = <<>>
        (* Process reader *)
        /\ current_message = [self \in { "r1", "r2" } |-> "none"]
        /\ pc = [self \in ProcSet |-> CASE self = "writer" -> "Write"
                                        [] self \in { "r1", "r2" } -> "Read"]

Write == /\ pc["writer"] = "Write"
         /\ Len(queue) < MaxQueueSize
         /\ queue' = Append(queue, "msg")
         /\ pc' = [pc EXCEPT !["writer"] = "Write"]
         /\ UNCHANGED current_message

writer == Write

Read(self) == /\ pc[self] = "Read"
              /\ queue /= <<>>
              /\ current_message' = [current_message EXCEPT ![self] = Head(queue)]
              /\ queue' = Tail(queue)
              /\ \/ /\ TRUE
                    /\ pc' = [pc EXCEPT ![self] = "Read"]
                 \/ /\ pc' = [pc EXCEPT ![self] = "NotifyFailure"]

NotifyFailure(self) == /\ pc[self] = "NotifyFailure"
                       /\ current_message' = [current_message EXCEPT ![self] = "none"]
                       /\ Len(queue) < MaxQueueSize
                       /\ queue' = Append(queue, self)
                       /\ pc' = [pc EXCEPT ![self] = "Read"]

reader(self) == Read(self) \/ NotifyFailure(self)

Next == writer
           \/ (\E self \in { "r1", "r2" }: reader(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Sat Oct 16 20:08:40 JST 2021 by yoshitsugu
\* Created Mon Oct 11 21:28:50 JST 2021 by yoshitsugu
