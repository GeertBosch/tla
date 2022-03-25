------------------------------ MODULE Derived ------------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets

\* This module models a method to keep in-memory derived metadata consistent 
\* with persisted collection data. The model includes snapshot and timestamp
\* semantics as implemented in MongoDB and the WiredTiger storage engine.
\* For simplicity model a single key/value store, and a single metadata value
\* representing the sum of all values.

\* To be set in model, see 'data' variable below.
CONSTANT InitData, InitTxns, ReadProc, WriteProc

\* Convert a sequence << a, b, ... >> to a set { a, b, ... }
RECURSIVE SeqToSet(_)
SeqToSet(seq) == IF seq = << >> THEN {} ELSE { Head(seq) } \cup SeqToSet(Tail(seq))

PickValueOr(set, default) == IF set = {} THEN default ELSE CHOOSE s \in set : {s} = set 
 
\* Reduction operator for Sequences and Sets
RECURSIVE SeqReduce(_, _, _)
SeqReduce(Op(_, _), seq, value) ==
   IF seq = <<>> THEN value
                 ELSE SeqReduce(Op, Tail(seq), Op(Head(seq), value))
RECURSIVE SetReduce(_, _, _)
SetReduce(Op(_, _), set, value) ==
   IF set = {} THEN value
               ELSE LET elem == (CHOOSE elem \in set : TRUE)
                    IN SetReduce (Op, set \ {elem}, Op(elem, value))
Sum(S) == LET sum(a, b) == a + b
          IN SeqReduce(sum, S, 0)
SumDataValues(data) == LET add(a, b) == a[3] + b
                       IN SetReduce(add, data, 0)

Key(data, key) == { d \in data : d[2] = key }
At(data, time) == { d \in data : d[1] =< time }
Last(data) == { d \in data : (\A d2 \in data : d2[2] /= d[2] \/ d2[1] <= d[1]) }

ReadAt(data, key, time) == Last(At(Key(data, key), time))
DeltaFor(snapshot, key, value) == value - PickValueOr(Last(Key(snapshot, key)), <<0, key, 0>>)[3]

IsVisible(snapshot, opTime) == \E op \in snapshot : op[1] = opTime
ReadMeta(meta, snapshot) == LET add(a, b) == b + (IF IsVisible(snapshot, a[1]) THEN a[2]
                                                                               ELSE 0)
                            IN SetReduce(add, meta, 0)
CheckMeta(meta, data) == ReadMeta(meta, data) = SumDataValues(Last(data))
MetaAt(meta, time) == { m \in meta : m[1] =< time }
allDurable(data) == { d \in data : /\ (\A t \in 1 .. d[1] : IsVisible(data, t))
                                   /\ ~IsVisible(data, d[1] + 1) }
\* `^\newpage^'
(*********

--algorithm Metadata {

variables
    \* Process Ids
    Proc = {1, 2};
    \* A set of transactions, each with a sequence of << key, value >> pairs to be upserted.
    txns = InitTxns,
    \* Set of keys with uncommitted writes pending.
    uncommitted = { },
    \* Set of all locally committed writes to the database as << optime, key, value >> tuples.
    data = InitData,
    \* `meta' is a set of <<optime, value >> pairs reflecting the in-memory derived metadata state.
    meta = { <<0, SumDataValues (data) >> },
    
    lastOpTime = 0;

    procedure Observe(opTime, snapshot, txn)
    { l1: 
        meta := meta \cup { << 
            opTime, 
            Sum([i \in 1 .. Len(txn) |-> DeltaFor(snapshot, txn[i][1], txn[i][2])])
        >> };
      l2: 
        return;
    }

    procedure ApplyOps(txn)
    variables
        snapshot,
        opTime,
        stmtId = 0;
    {
      write:
        \* Purposefully non-atomic to mimic WiredTiger behavior. Model only states without
        \* WriteConflictExceptions: verifying that those don't affect state is out of scope.
        while (stmtId < Len(txn)) {
            stmtId := stmtId + 1;
            await ~(txn[stmtId][1] \in uncommitted);
            uncommitted := uncommitted \cup {txn[stmtId][1]};
        };
        \* While in actuallity we would get the snapshot before marking the key as having updates
        \* and get a new snapshot on each retry, this is in fact the same as we don't need the actual
        \* snapshot until later.
        snapshot := data;

      nextOpTime:
        lastOpTime := lastOpTime + 1;
        opTime := lastOpTime;
      observe:
        call Observe(opTime, snapshot, txn);
      commitTransaction:
        data := data \cup SeqToSet([ i \in 1 .. Len(txn) |-> << opTime >> \o txn[i] ]);
        uncommitted := { key \in uncommitted : \A i \in 1 .. Len(txn) : txn[i][1] /= key };
      onCommit:
        return;
    };
    
    process (reader \in ReadProc)
    variables
        snapshot = data;
    { l1: 
        assert ReadMeta(meta, snapshot) = SumDataValues(Last(snapshot));
    }

    process (writer \in WriteProc)
    {
    l1: while (txns # {}) {
            with (nextTxn \in txns) {
                txns := txns \ { nextTxn } ;
                call ApplyOps(nextTxn);
            }
        }
    }
}

********)
\* `^\newpage^'
\* BEGIN TRANSLATION (chksum(pcal) = "c3c2ecb2" /\ chksum(tla) = "fd96bfd9")
\* Label l1 of procedure Observe at line 68 col 7 changed to l1_
\* Label l1 of process reader at line 112 col 9 changed to l1_r
\* Process variable snapshot of process reader at line 110 col 9 changed to snapshot_
\* Procedure variable snapshot of procedure ApplyOps at line 78 col 9 changed to snapshot_A
\* Procedure variable opTime of procedure ApplyOps at line 79 col 9 changed to opTime_
\* Parameter txn of procedure Observe at line 66 col 41 changed to txn_
CONSTANT defaultInitValue
VARIABLES Proc, txns, uncommitted, data, meta, lastOpTime, pc, stack, opTime, 
          snapshot, txn_, txn, snapshot_A, opTime_, stmtId, snapshot_

vars == << Proc, txns, uncommitted, data, meta, lastOpTime, pc, stack, opTime, 
           snapshot, txn_, txn, snapshot_A, opTime_, stmtId, snapshot_ >>

ProcSet == (ReadProc) \cup (WriteProc)

Init == (* Global variables *)
        /\ Proc = {1, 2}
        /\ txns = InitTxns
        /\ uncommitted = { }
        /\ data = InitData
        /\ meta = { <<0, SumDataValues (data) >> }
        /\ lastOpTime = 0
        (* Procedure Observe *)
        /\ opTime = [ self \in ProcSet |-> defaultInitValue]
        /\ snapshot = [ self \in ProcSet |-> defaultInitValue]
        /\ txn_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure ApplyOps *)
        /\ txn = [ self \in ProcSet |-> defaultInitValue]
        /\ snapshot_A = [ self \in ProcSet |-> defaultInitValue]
        /\ opTime_ = [ self \in ProcSet |-> defaultInitValue]
        /\ stmtId = [ self \in ProcSet |-> 0]
        (* Process reader *)
        /\ snapshot_ = [self \in ReadProc |-> data]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in ReadProc -> "l1_r"
                                        [] self \in WriteProc -> "l1"]

l1_(self) == /\ pc[self] = "l1_"
             /\ meta' = (      meta \cup { <<
                             opTime[self],
                            Sum([i \in 1 .. Len(txn_[self]) |-> DeltaFor(snapshot[self], txn_[self][i][1], txn_[self][i][2])])
                         >> })
             /\ pc' = [pc EXCEPT ![self] = "l2"]
             /\ UNCHANGED << Proc, txns, uncommitted, data, lastOpTime, stack, 
                             opTime, snapshot, txn_, txn, snapshot_A, opTime_, 
                             stmtId, snapshot_ >>

l2(self) == /\ pc[self] = "l2"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ opTime' = [opTime EXCEPT ![self] = Head(stack[self]).opTime]
            /\ snapshot' = [snapshot EXCEPT ![self] = Head(stack[self]).snapshot]
            /\ txn_' = [txn_ EXCEPT ![self] = Head(stack[self]).txn_]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << Proc, txns, uncommitted, data, meta, lastOpTime, 
                            txn, snapshot_A, opTime_, stmtId, snapshot_ >>

Observe(self) == l1_(self) \/ l2(self)

write(self) == /\ pc[self] = "write"
               /\ IF stmtId[self] < Len(txn[self])
                     THEN /\ stmtId' = [stmtId EXCEPT ![self] = stmtId[self] + 1]
                          /\ ~(txn[self][stmtId'[self]][1] \in uncommitted)
                          /\ uncommitted' = (uncommitted \cup {txn[self][stmtId'[self]][1]})
                          /\ pc' = [pc EXCEPT ![self] = "write"]
                          /\ UNCHANGED snapshot_A
                     ELSE /\ snapshot_A' = [snapshot_A EXCEPT ![self] = data]
                          /\ pc' = [pc EXCEPT ![self] = "nextOpTime"]
                          /\ UNCHANGED << uncommitted, stmtId >>
               /\ UNCHANGED << Proc, txns, data, meta, lastOpTime, stack, 
                               opTime, snapshot, txn_, txn, opTime_, snapshot_ >>

nextOpTime(self) == /\ pc[self] = "nextOpTime"
                    /\ lastOpTime' = lastOpTime + 1
                    /\ opTime_' = [opTime_ EXCEPT ![self] = lastOpTime']
                    /\ pc' = [pc EXCEPT ![self] = "observe"]
                    /\ UNCHANGED << Proc, txns, uncommitted, data, meta, stack, 
                                    opTime, snapshot, txn_, txn, snapshot_A, 
                                    stmtId, snapshot_ >>

observe(self) == /\ pc[self] = "observe"
                 /\ /\ opTime' = [opTime EXCEPT ![self] = opTime_[self]]
                    /\ snapshot' = [snapshot EXCEPT ![self] = snapshot_A[self]]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Observe",
                                                             pc        |->  "commitTransaction",
                                                             opTime    |->  opTime[self],
                                                             snapshot  |->  snapshot[self],
                                                             txn_      |->  txn_[self] ] >>
                                                         \o stack[self]]
                    /\ txn_' = [txn_ EXCEPT ![self] = txn[self]]
                 /\ pc' = [pc EXCEPT ![self] = "l1_"]
                 /\ UNCHANGED << Proc, txns, uncommitted, data, meta, 
                                 lastOpTime, txn, snapshot_A, opTime_, stmtId, 
                                 snapshot_ >>

commitTransaction(self) == /\ pc[self] = "commitTransaction"
                           /\ data' = (data \cup SeqToSet([ i \in 1 .. Len(txn[self]) |-> << opTime_[self] >> \o txn[self][i] ]))
                           /\ uncommitted' = { key \in uncommitted : \A i \in 1 .. Len(txn[self]) : txn[self][i][1] /= key }
                           /\ pc' = [pc EXCEPT ![self] = "onCommit"]
                           /\ UNCHANGED << Proc, txns, meta, lastOpTime, stack, 
                                           opTime, snapshot, txn_, txn, 
                                           snapshot_A, opTime_, stmtId, 
                                           snapshot_ >>

onCommit(self) == /\ pc[self] = "onCommit"
                  /\ Assert(CheckMeta(meta, snapshot_A[self]), 
                            "Failure of assertion at line 104, column 9.")
                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                  /\ snapshot_A' = [snapshot_A EXCEPT ![self] = Head(stack[self]).snapshot_A]
                  /\ opTime_' = [opTime_ EXCEPT ![self] = Head(stack[self]).opTime_]
                  /\ stmtId' = [stmtId EXCEPT ![self] = Head(stack[self]).stmtId]
                  /\ txn' = [txn EXCEPT ![self] = Head(stack[self]).txn]
                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                  /\ UNCHANGED << Proc, txns, uncommitted, data, meta, 
                                  lastOpTime, opTime, snapshot, txn_, 
                                  snapshot_ >>

ApplyOps(self) == write(self) \/ nextOpTime(self) \/ observe(self)
                     \/ commitTransaction(self) \/ onCommit(self)

l1_r(self) == /\ pc[self] = "l1_r"
              /\ Assert(ReadMeta(meta, snapshot_[self]) = SumDataValues(Last(snapshot_[self])), 
                        "Failure of assertion at line 112, column 9.")
              /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << Proc, txns, uncommitted, data, meta, lastOpTime, 
                              stack, opTime, snapshot, txn_, txn, snapshot_A, 
                              opTime_, stmtId, snapshot_ >>

reader(self) == l1_r(self)

l1(self) == /\ pc[self] = "l1"
            /\ IF txns # {}
                  THEN /\ \E nextTxn \in txns:
                            /\ txns' = txns \ { nextTxn }
                            /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ApplyOps",
                                                                        pc        |->  "l1",
                                                                        snapshot_A |->  snapshot_A[self],
                                                                        opTime_   |->  opTime_[self],
                                                                        stmtId    |->  stmtId[self],
                                                                        txn       |->  txn[self] ] >>
                                                                    \o stack[self]]
                               /\ txn' = [txn EXCEPT ![self] = nextTxn]
                            /\ snapshot_A' = [snapshot_A EXCEPT ![self] = defaultInitValue]
                            /\ opTime_' = [opTime_ EXCEPT ![self] = defaultInitValue]
                            /\ stmtId' = [stmtId EXCEPT ![self] = 0]
                            /\ pc' = [pc EXCEPT ![self] = "write"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << txns, stack, txn, snapshot_A, opTime_, 
                                       stmtId >>
            /\ UNCHANGED << Proc, uncommitted, data, meta, lastOpTime, opTime, 
                            snapshot, txn_, snapshot_ >>

writer(self) == l1(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: Observe(self) \/ ApplyOps(self))
           \/ (\E self \in ReadProc: reader(self))
           \/ (\E self \in WriteProc: writer(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Fri Mar 25 17:50:22 EDT 2022 by bosch
\* Created Mon Mar 14 08:30:23 EDT 2022 by bosch
