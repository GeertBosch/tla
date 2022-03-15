------------------------------ MODULE Derived ------------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets

\* To be set in model, see 'data' variable below.
CONSTANT InitData

Key(data, key) == { d \in data : d[2] = key }
At(data, time) == { d \in data : d[1] =< time }
Last(data) == { d \in data : (~\E d2 \in data : d2[1] > d[1]) }

ReadAt(data, key, time) == Last(At(Key(data, key), time))

(*********

--algorithm Metadata {

variables
    \* Process Ids
    Proc = {1};
    \* These model << key, value >> pairs to be upserted
    ops = { << "x", 1>>, << "y", 3>>, << "x", 7>>, << "y", 1>>, << "x", 0>> },
    \* Set of keys with uncommitted writes pending
    uncommitted = { },
    \* Set of all writes to the database as << optime, key, value >> pairs
    data = InitData,
    \* meta is set of << optime, delta >> pairs
    meta = { <<0, 1>> },
    lastOptime = 0;
     
    procedure Observe(logop)
    {
    l1:
    
       \* meta := meta \cup logop;
       return;
    };
 
    procedure WriteOp(op)
    variables
        logop = { };

    {
    l2:
        await ~(op[1] \in uncommitted);
        uncommitted := uncommitted \cup {op[1]};
        lastOptime := lastOptime + 1;
        logop := << lastOptime, op[1], op[2] >>;
    observe:
        call Observe(logop);
    commit:
        uncommitted := uncommitted \ { op[1] };
        data := data \cup { logop };
    onCommit:
        return;
    };
    
    process (p \in Proc) 
    {
        l3:
        while (ops # {}) { 
            with (nextOp \in ops) {
                ops := ops \ { nextOp } ;
                call WriteOp(nextOp);
            }
        }
    }  
}
   
********)
\* BEGIN TRANSLATION (chksum(pcal) = "c0ac92e1" /\ chksum(tla) = "bfd903c9")
\* Procedure variable logop of procedure WriteOp at line 39 col 9 changed to logop_
CONSTANT defaultInitValue
VARIABLES Proc, ops, uncommitted, data, meta, lastOptime, pc, stack, logop, 
          op, logop_

vars == << Proc, ops, uncommitted, data, meta, lastOptime, pc, stack, logop, 
           op, logop_ >>

ProcSet == (Proc)

Init == (* Global variables *)
        /\ Proc = {1}
        /\ ops = { << "x", 1>>, << "y", 3>>, << "x", 7>>, << "y", 1>>, << "x", 0>> }
        /\ uncommitted = { }
        /\ data = InitData
        /\ meta = { <<0, 1>> }
        /\ lastOptime = 0
        (* Procedure Observe *)
        /\ logop = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure WriteOp *)
        /\ op = [ self \in ProcSet |-> defaultInitValue]
        /\ logop_ = [ self \in ProcSet |-> { }]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "l3"]

l1(self) == /\ pc[self] = "l1"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ logop' = [logop EXCEPT ![self] = Head(stack[self]).logop]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << Proc, ops, uncommitted, data, meta, lastOptime, op, 
                            logop_ >>

Observe(self) == l1(self)

l2(self) == /\ pc[self] = "l2"
            /\ ~(op[self][1] \in uncommitted)
            /\ uncommitted' = (uncommitted \cup {op[self][1]})
            /\ lastOptime' = lastOptime + 1
            /\ logop_' = [logop_ EXCEPT ![self] = << lastOptime', op[self][1], op[self][2] >>]
            /\ pc' = [pc EXCEPT ![self] = "observe"]
            /\ UNCHANGED << Proc, ops, data, meta, stack, logop, op >>

observe(self) == /\ pc[self] = "observe"
                 /\ /\ logop' = [logop EXCEPT ![self] = logop_[self]]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Observe",
                                                             pc        |->  "commit",
                                                             logop     |->  logop[self] ] >>
                                                         \o stack[self]]
                 /\ pc' = [pc EXCEPT ![self] = "l1"]
                 /\ UNCHANGED << Proc, ops, uncommitted, data, meta, 
                                 lastOptime, op, logop_ >>

commit(self) == /\ pc[self] = "commit"
                /\ uncommitted' = uncommitted \ { op[self][1] }
                /\ data' = (data \cup { logop_[self] })
                /\ pc' = [pc EXCEPT ![self] = "onCommit"]
                /\ UNCHANGED << Proc, ops, meta, lastOptime, stack, logop, op, 
                                logop_ >>

onCommit(self) == /\ pc[self] = "onCommit"
                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                  /\ logop_' = [logop_ EXCEPT ![self] = Head(stack[self]).logop_]
                  /\ op' = [op EXCEPT ![self] = Head(stack[self]).op]
                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                  /\ UNCHANGED << Proc, ops, uncommitted, data, meta, 
                                  lastOptime, logop >>

WriteOp(self) == l2(self) \/ observe(self) \/ commit(self)
                    \/ onCommit(self)

l3(self) == /\ pc[self] = "l3"
            /\ IF ops # {}
                  THEN /\ \E nextOp \in ops:
                            /\ ops' = ops \ { nextOp }
                            /\ /\ op' = [op EXCEPT ![self] = nextOp]
                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "WriteOp",
                                                                        pc        |->  "l3",
                                                                        logop_    |->  logop_[self],
                                                                        op        |->  op[self] ] >>
                                                                    \o stack[self]]
                            /\ logop_' = [logop_ EXCEPT ![self] = { }]
                            /\ pc' = [pc EXCEPT ![self] = "l2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << ops, stack, op, logop_ >>
            /\ UNCHANGED << Proc, uncommitted, data, meta, lastOptime, logop >>

p(self) == l3(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: Observe(self) \/ WriteOp(self))
           \/ (\E self \in Proc: p(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Tue Mar 15 19:00:08 EDT 2022 by bosch
\* Created Mon Mar 14 08:30:23 EDT 2022 by bosch
