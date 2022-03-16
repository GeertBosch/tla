------------------------------ MODULE Derived ------------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets

\* To be set in model, see 'data' variable below.
CONSTANT InitData, InitTxns

\* Convert a sequence << a, b, ... >> to a set { a, b, ... }
RECURSIVE SeqToSet(_)
SeqToSet(seq) == IF seq = << >> THEN {} ELSE { Head(seq) } \cup SeqToSet(Tail(seq))


\* Reduction operator
RECURSIVE SetReduce(_, _, _)
SetReduce(Op(_, _), S, value) ==
   IF S = {} THEN value
             ELSE LET s == (CHOOSE s \in S : TRUE) IN SetReduce(Op, S \ {s}, Op(s, value))

Sum(S) == LET sum(a, b) == a + b IN SetReduce(sum, S, 0)

SumDataValues(data) == LET add(a, b) == a[3] + b IN SetReduce(add, data, 0)

Key(data, key) == { d \in data : d[2] = key }
At(data, time) == { d \in data : d[1] =< time }
Last(data) == { d \in data : (~\E d2 \in data : d2[1] > d[1]) }

ReadAt(data, key, time) == Last(At(Key(data, key), time))

(*********

--algorithm Metadata {

variables
    \* Process Ids
    Proc = {1, 2};
    \* A set of transactions, each with a sequence of << key, value >> pairs to be upserted
    txns = InitTxns,

    \* Set of keys with uncommitted writes pending
    uncommitted = { },
    \* Set of all locally committed writes to the database as << optime, key, value >> pairs
    data = InitData,
    \* meta is set of <<optime, value >> pairs reflecting
    \*
    meta = { <<0, SumDataValues (data) >> },
    lastOpTime = 0
    ;

    procedure Observe(opTime, snapshot, txn)
    variables
        delta;
    {
    l1:
        \* delta := [ i \in 1 .. Len(txn) |-> txn[i][2] - Pick(Last(Key(snapshot, txn[i][1]))[3]];
        \* meta := meta \cup { << opTime, Sum(SeqToSet(delta)) >> };

       return;
    };

    procedure ApplyOps(txn)
    variables
        snapshot = data,
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

    nextOpTime:
        lastOpTime := lastOpTime + 1;
        opTime := lastOpTime;
    observe:
        call Observe(opTime, snapshot, txn);
    commitTransaction:
        uncommitted := { key \in uncommitted : (\A i \in 1 .. Len(txn) : txn[i][1] /= key) };
        data := data \cup SeqToSet([ i \in 1 .. Len(txn) |-> << opTime >> \o txn[i] ]);
    onCommit:
        return;
    };

    process (writer \in Proc)
    {
        l3:
        while (txns # {}) {
            with (nextTxn \in txns) {
                txns := txns \ { nextTxn } ;
                call ApplyOps(nextTxn);
            }
        }
    }
}

********)

\* BEGIN TRANSLATION (chksum(pcal) = "c3ae71bf" /\ chksum(tla) = "aa673078")
\* Procedure variable snapshot of procedure ApplyOps at line 61 col 9 changed to snapshot_
\* Procedure variable opTime of procedure ApplyOps at line 62 col 9 changed to opTime_
\* Parameter txn of procedure Observe at line 48 col 41 changed to txn_
CONSTANT defaultInitValue
VARIABLES Proc, txns, uncommitted, data, meta, lastOpTime, pc, stack, opTime,
          snapshot, txn_, delta, txn, snapshot_, opTime_, stmtId

vars == << Proc, txns, uncommitted, data, meta, lastOpTime, pc, stack, opTime,
           snapshot, txn_, delta, txn, snapshot_, opTime_, stmtId >>

ProcSet == (Proc)

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
        /\ delta = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure ApplyOps *)
        /\ txn = [ self \in ProcSet |-> defaultInitValue]
        /\ snapshot_ = [ self \in ProcSet |-> data]
        /\ opTime_ = [ self \in ProcSet |-> defaultInitValue]
        /\ stmtId = [ self \in ProcSet |-> 0]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "l3"]

l1(self) == /\ pc[self] = "l1"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ delta' = [delta EXCEPT ![self] = Head(stack[self]).delta]
            /\ opTime' = [opTime EXCEPT ![self] = Head(stack[self]).opTime]
            /\ snapshot' = [snapshot EXCEPT ![self] = Head(stack[self]).snapshot]
            /\ txn_' = [txn_ EXCEPT ![self] = Head(stack[self]).txn_]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << Proc, txns, uncommitted, data, meta, lastOpTime,
                            txn, snapshot_, opTime_, stmtId >>

Observe(self) == l1(self)

write(self) == /\ pc[self] = "write"
               /\ IF stmtId[self] < Len(txn[self])
                     THEN /\ stmtId' = [stmtId EXCEPT ![self] = stmtId[self] + 1]
                          /\ ~(txn[self][stmtId'[self]][1] \in uncommitted)
                          /\ uncommitted' = (uncommitted \cup {txn[self][stmtId'[self]][1]})
                          /\ pc' = [pc EXCEPT ![self] = "write"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "nextOpTime"]
                          /\ UNCHANGED << uncommitted, stmtId >>
               /\ UNCHANGED << Proc, txns, data, meta, lastOpTime, stack,
                               opTime, snapshot, txn_, delta, txn, snapshot_,
                               opTime_ >>

nextOpTime(self) == /\ pc[self] = "nextOpTime"
                    /\ lastOpTime' = lastOpTime + 1
                    /\ opTime_' = [opTime_ EXCEPT ![self] = lastOpTime']
                    /\ pc' = [pc EXCEPT ![self] = "observe"]
                    /\ UNCHANGED << Proc, txns, uncommitted, data, meta, stack,
                                    opTime, snapshot, txn_, delta, txn,
                                    snapshot_, stmtId >>

observe(self) == /\ pc[self] = "observe"
                 /\ /\ opTime' = [opTime EXCEPT ![self] = opTime_[self]]
                    /\ snapshot' = [snapshot EXCEPT ![self] = snapshot_[self]]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Observe",
                                                             pc        |->  "commitTransaction",
                                                             delta     |->  delta[self],
                                                             opTime    |->  opTime[self],
                                                             snapshot  |->  snapshot[self],
                                                             txn_      |->  txn_[self] ] >>
                                                         \o stack[self]]
                    /\ txn_' = [txn_ EXCEPT ![self] = txn[self]]
                 /\ delta' = [delta EXCEPT ![self] = defaultInitValue]
                 /\ pc' = [pc EXCEPT ![self] = "l1"]
                 /\ UNCHANGED << Proc, txns, uncommitted, data, meta,
                                 lastOpTime, txn, snapshot_, opTime_, stmtId >>

commitTransaction(self) == /\ pc[self] = "commitTransaction"
                           /\ uncommitted' = { key \in uncommitted : (\A i \in 1 .. Len(txn[self]) : txn[self][i][1] /= key) }
                           /\ data' = (data \cup SeqToSet([ i \in 1 .. Len(txn[self]) |-> << opTime_[self] >> \o txn[self][i] ]))
                           /\ pc' = [pc EXCEPT ![self] = "onCommit"]
                           /\ UNCHANGED << Proc, txns, meta, lastOpTime, stack,
                                           opTime, snapshot, txn_, delta, txn,
                                           snapshot_, opTime_, stmtId >>

onCommit(self) == /\ pc[self] = "onCommit"
                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                  /\ snapshot_' = [snapshot_ EXCEPT ![self] = Head(stack[self]).snapshot_]
                  /\ opTime_' = [opTime_ EXCEPT ![self] = Head(stack[self]).opTime_]
                  /\ stmtId' = [stmtId EXCEPT ![self] = Head(stack[self]).stmtId]
                  /\ txn' = [txn EXCEPT ![self] = Head(stack[self]).txn]
                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                  /\ UNCHANGED << Proc, txns, uncommitted, data, meta,
                                  lastOpTime, opTime, snapshot, txn_, delta >>

ApplyOps(self) == write(self) \/ nextOpTime(self) \/ observe(self)
                     \/ commitTransaction(self) \/ onCommit(self)

l3(self) == /\ pc[self] = "l3"
            /\ IF txns # {}
                  THEN /\ \E nextTxn \in txns:
                            /\ txns' = txns \ { nextTxn }
                            /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ApplyOps",
                                                                        pc        |->  "l3",
                                                                        snapshot_ |->  snapshot_[self],
                                                                        opTime_   |->  opTime_[self],
                                                                        stmtId    |->  stmtId[self],
                                                                        txn       |->  txn[self] ] >>
                                                                    \o stack[self]]
                               /\ txn' = [txn EXCEPT ![self] = nextTxn]
                            /\ snapshot_' = [snapshot_ EXCEPT ![self] = data]
                            /\ opTime_' = [opTime_ EXCEPT ![self] = defaultInitValue]
                            /\ stmtId' = [stmtId EXCEPT ![self] = 0]
                            /\ pc' = [pc EXCEPT ![self] = "write"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << txns, stack, txn, snapshot_, opTime_,
                                       stmtId >>
            /\ UNCHANGED << Proc, uncommitted, data, meta, lastOpTime, opTime,
                            snapshot, txn_, delta >>

writer(self) == l3(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: Observe(self) \/ ApplyOps(self))
           \/ (\E self \in Proc: writer(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Wed Mar 16 18:34:43 EDT 2022 by bosch
\* Created Mon Mar 14 08:30:23 EDT 2022 by bosch
