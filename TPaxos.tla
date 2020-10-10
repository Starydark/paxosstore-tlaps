------------------------------ MODULE TPaxos --------------------------------
(*
Specification of the consensus protocol in PaxosStore.
See [PaxosStore@VLDB2017](https://www.vldb.org/pvldb/vol10/p1730-lin.pdf) 
by Tencent.
In this version (adopted from "PaxosStore.tla"):
- Client-restricted config (Ballot)
- Message types (i.e., "Prepare", "Accept", "ACK") are deleted.
No state flags (such as "Prepare", "Wait-Prepare", "Accept", "Wait-Accept"
are needed.
- Choose value from a quorum in Accept.
*)
EXTENDS Integers, FiniteSets, TLAPS
-----------------------------------------------------------------------------
Max(m, n) == IF m > n THEN m ELSE n
Injective(f) == \A a, b \in DOMAIN f: (a # b) => (f[a] # f[b])
-----------------------------------------------------------------------------
CONSTANTS 
    Participant,  \* the set of partipants
    Value         \* the set of possible input values for Participant to propose
           
None == CHOOSE b : b \notin Value
NP == Cardinality(Participant) \* number of p \in Participants

Quorum == {Q \in SUBSET Participant : Cardinality(Q) * 2 >= NP + 1}
ASSUME QuorumAssumption == 
    /\ \A Q \in Quorum : Q \subseteq Participant
    /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

Ballot == Nat

MaxBallot == Cardinality(Ballot) - 1

PIndex == CHOOSE f \in [Participant -> 1 .. NP] : Injective(f)
Bals(p) == {b \in Ballot : b % NP = PIndex[p] - 1} \* allocate ballots for each p \in Participant
-----------------------------------------------------------------------------
State == [maxBal: Ballot \cup {-1},
         maxVBal: Ballot \cup {-1}, maxVVal: Value \cup {None}]

InitState == [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None]
(*
For simplicity, in this specification, we choose to send the complete state
of a participant each time. When receiving such a message, the participant 
processes only the "partial" state it needs.
*)
Message == [from: Participant, to : SUBSET Participant, state: [Participant -> State]]
-----------------------------------------------------------------------------
VARIABLES 
    state,  \* state[p][q]: the state of q \in Participant from the view of p \in Participant
    msgs    \* the set of messages that have been sent

vars == <<state, msgs>>
          
TypeOK == 
    /\ state \in [Participant -> [Participant -> State]]
    /\ msgs \subseteq Message

Send(m) == msgs' = msgs \cup {m}
-----------------------------------------------------------------------------
Init == 
    /\ state = [p \in Participant |-> [q \in Participant |-> InitState]] 
    /\ msgs = {}
(*
p \in Participant starts the prepare phase by issuing a ballot b \in Ballot.
*)
Prepare(p, b) == 
    /\ b \in Bals(p)
    /\ state[p][p].maxBal < b
    /\ state' = [state EXCEPT ![p][p].maxBal = b]
    /\ Send([from |-> p, to |-> Participant \ {p}, state |-> state'[p]])                 
(*
q \in Participant updates its own state state[q] according to the actual state
pp of p \in Participant extracted from a message m \in Message it receives. 
This is called by OnMessage(q).
Note: pp is m.state[p]; it may not be equal to state[p][p] at the time 
UpdateState is called.
*)
UpdateState(q, p, pp) == 
    LET maxB == Max(state[q][q].maxBal, pp.maxBal)
    IN  state' = [state EXCEPT 
                  ![q][p].maxBal = Max(@, pp.maxBal),
                  ![q][p].maxVBal = Max(@, pp.maxVBal),
                  ![q][p].maxVVal = IF state[q][p].maxVBal < pp.maxVBal 
                                    THEN pp.maxVVal ELSE @,
                  ![q][q].maxBal = maxB, \* make promise first and then accept
                  ![q][q].maxVBal = IF maxB <= pp.maxVBal  \* accept
                                    THEN pp.maxVBal ELSE @, 
                  ![q][q].maxVVal = IF maxB <= pp.maxVBal  \* accept
                                    THEN pp.maxVVal ELSE @]  
(*
q \in Participant receives and processes a message in Message.
*)
OnMessage(q) == 
    \E m \in msgs : 
        /\ q \in m.to
        /\ LET p == m.from
           IN  UpdateState(q, p, m.state[p])
        /\ LET qm == [from |-> m.from, to |-> m.to \ {q}, state |-> m.state] \*remove q from to
               nm == [from |-> q, to |-> {m.from}, state |-> state'[q]] \*new message to reply
           IN  IF \/ m.state[q].maxBal < state'[q][q].maxBal
                  \/ m.state[q].maxVBal < state'[q][q].maxVBal
               THEN msgs' = (msgs \ {m}) \cup {qm, nm} 
               ELSE msgs' = (msgs \ {m}) \cup {qm}
(*
p \in Participant starts the accept phase by issuing the ballot b \in Ballot
with value v \in Value.
*)
Accept(p, b, v) == 
    /\ b \in Bals(p)
    /\ state[p][p].maxBal <= b \*corresponding the first conjunction in Voting
    /\ state[p][p].maxVBal # b \* correspongding the second conjunction in Voting
    /\ \E Q \in Quorum : 
       /\ \A q \in Q : state[p][q].maxBal = b
       \* pick the value from the quorum
       (*/\ \/ \A q \in Q : state[p][q].maxVBal = -1 \* free to pick its own value
          \/ \E q \in Q : \* v is the value with the highest maxVBal in the quorum
                /\ state[p][q].maxVVal = v
                /\ \A r \in Q : state[p][q].maxVBal >= state[p][r].maxVBal
        *)
    \*choose the value from all the local state
    /\ \/ \A q \in Participant : state[p][q].maxVBal = -1 \* free to pick its own value
       \/ \E q \in Participant : \* v is the value with the highest maxVBal
            /\ state[p][q].maxVVal = v 
            /\ \A r \in Participant: state[p][q].maxVBal >= state[p][r].maxVBal
    /\ state' = [state EXCEPT ![p][p].maxVBal = b,
                              ![p][p].maxVVal = v]
    /\ Send([from |-> p, to |-> Participant \ {p}, state |-> state'[p]])
---------------------------------------------------------------------------
Next == \E p \in Participant : \/ OnMessage(p)
                               \/ \E b \in Ballot : \/ Prepare(p, b)
                                                    \/ \E v \in Value : Accept(p, b, v)
Spec == Init /\ [][Next]_vars
---------------------------------------------------------------------------
VotedForIn(a, b, v) == \E m \in msgs:
                            /\ m.from = a
                            /\ m.state[a].maxBal = b
                            /\ m.state[a].maxVBal = b
                            /\ m.state[a].maxVVal = v

ChosenIn(b, v) == \E Q \in Quorum:
                    \A a \in Q: VotedForIn(a, b, v)
                    
Chosen(v) == \E b \in Ballot: ChosenIn(b, v)

ChosenP(p) == \* the set of values chosen by p \in Participant
    {v \in Value : \E b \in Ballot : 
                       \E Q \in Quorum: \A q \in Q: /\ state[p][q].maxVBal = b
                                                    /\ state[p][q].maxVVal = v}

chosen == UNION {ChosenP(p) : p \in Participant}

Consistency == \*Cardinality(chosen) <= 1   
   \A v1, v2 \in Value: Chosen(v1) /\ Chosen(v2) => (v1 = v2)

---------------------------------------------------------------------------
WontVoteIn(a, b) == /\ \A v \in Value: ~ VotedForIn(a, b, v)
                    /\ state[a][a].maxBal > a

SafeAt(b, v) == 
        \A c \in 0..(b-1):
            \E Q \in Quorum:
                \A a \in Q: VotedForIn(a, c, v) \/ WontVoteIn(a, c)

---------------------------------------------------------------------------
MsgInv == 
    \A m \in msgs:
        LET p == m.from
            curState == m.state[p]
         IN /\ curState.maxBal # curState.maxVBal 
                => /\ curState.maxBal < state[p][p].maxBal
                   /\ \/ /\ curState.maxVVal \in Value
                         /\ curState.maxVBal \in Ballot
                         \*/\ VotedForIn(curState.maxVBal, curState.maxVVal)
                      \/ /\ curState.maxVVal = None
                         /\ curState.maxVBal = -1
                   /\ \A c \in (curState.maxVBal + 1)..(curState.maxBal - 1):
                        ~ \E v \in Value: VotedForIn(p, c, v)
            /\ curState.maxBal = curState.maxVBal \* exclude (-1,-1,None)
                => /\ SafeAt(curState.maxVBal, curState.maxVVal)
                   /\ \A ma \in msgs: (ma.state[ma.from].maxBal = curState.maxBal
                                       /\ ma.state[ma.from].maxBal = ma.state[ma.from].maxVBal)
                                    => ma.state[ma.from].maxVVal = curState.maxVVal
                                    
AccInv ==  
    \A a \in Participant:
        /\ (state[a][a].maxVBal = -1) <=> (state[a][a].maxVVal = None)
        /\ state[a][a].maxVBal <= state[a][a].maxBal
        /\ (state[a][a].maxVBal >= 0) => VotedForIn(a, state[a][a].maxVBal, state[a][a].maxVVal)
        /\ \A c \in Ballot: c > state[a][a].maxVBal 
            => ~ \E v \in Value: VotedForIn(a, c, v)
            
Inv == MsgInv /\ AccInv /\ TypeOK
--------------------------------------------------------------------------
LEMMA VotedInv == 
        MsgInv /\ TypeOK =>
            \A a \in Participant, b \in Ballot, v \in Value:
                VotedForIn(a, b, v) => SafeAt(b, v)
BY DEFS MsgInv, VotedForIn, Message, TypeOK

LEMMA VotedOnce == 
        MsgInv => \A a1, a2 \in Participant, b \in Ballot, v1, v2 \in Value:
                VotedForIn(a1, b, v1) /\ VotedForIn(a2, b, v2) => (v1 = v2)
BY DEFS MsgInv, VotedForIn
--------------------------------------------------------------------------
LEMMA SafeAtStable == Inv /\ Next /\ TypeOK' =>
                            \A v \in Value, b \in Ballot:
                               SafeAt(b, v) => SafeAt(b, v)'
<1> SUFFICES ASSUME Inv, Next, TypeOK',
                        NEW b \in Ballot, NEW v \in Value,
                        SafeAt(b, v)
                 PROVE  SafeAt(b, v)'
    OBVIOUS
<1> USE DEFS Inv, Send, Ballot, TypeOK
<1>1. ASSUME NEW pp \in Participant, NEW bb \in Ballot, Prepare(pp, bb), TypeOK
      PROVE SafeAt(b, v)'
\*      BY <1>1, QuorumAssumption DEFS Prepare, SafeAt, TypeOK, VotedForIn, WontVoteIn
  <2>1. \A p1 \in Participant, b1 \in Ballot, v1 \in Value:
        VotedForIn(p1, b1, v1) => VotedForIn(p1, b1, v1)'
    BY <1>1 DEFS VotedForIn, Prepare
  <2>2. \A p1 \in Participant, b1 \in Ballot:
        state[p1][p1].maxBal > b1 => state'[p1][p1].maxBal > b1
    BY <1>1, QuorumAssumption DEFS TypeOK, Prepare, State
  <2>3. \A p1 \in Participant, b1 \in Ballot, v1 \in Value:
        ~ VotedForIn(p1, b1, v1) => ~ VotedForIn(p1, b1, v1)'
    BY <1>1 DEFS Prepare, AccInv, VotedForIn
  <2>4. \A p1 \in Participant, b1 \in Ballot:
        WontVoteIn(p1, b1) => WontVoteIn(p1, b1)'
    BY <2>1, <2>2, QuorumAssumption DEFS TypeOK, Prepare, WontVoteIn
  <2>6. QED    
   BY <1>1, QuorumAssumption DEFS Prepare, SafeAt, VotedForIn, WontVoteIn, TypeOK
<1>2. ASSUME NEW pp \in Participant, NEW bb \in Ballot, NEW vv \in Value,
             Accept(pp, bb, vv)
      PROVE SafeAt(b, v)'
<1>3. ASSUME NEW pp \in Participant, OnMessage(pp)
      PROVE SafeAt(b, v)'
<1> QED   
  BY <1>1, <1>2, <1>3 DEF Next

VARIABLES num, arr
TypeOK1 == /\ num \in Nat
           /\ arr \in [Participant -> Nat]

INC(b) ==
    /\ b \in Nat
    /\ num < b
    /\ num' = b
    
LEMMA REC == \A a \in Nat, b \in Nat, c \in Nat:
                b > a /\ c > b => c > a

INC1(p, b) ==
    /\ b \in Bals(p)
    /\ state[p][p].maxBal < b
    /\ state' = [state EXCEPT ![p][p].maxBal = b]
    
LEMMA INCAlaywaysInc == \E b \in Nat: INC(b) /\ TypeOK1 =>
    \A b2 \in Nat: num > b2 => num' > b2
    \*            state[p1][p1].maxBal > b2 => state'[p1][p1].maxBal > b2 
<1> SUFFICES ASSUME NEW bb \in Nat, NEW b2 \in Nat, INC(bb), num > b2, TypeOK1
        PROVE num' > b2
    OBVIOUS
<1>1. CASE bb > b2
    BY <1>1 DEFS INC
<1>2. CASE bb <= b2
   <2> SUFFICES ASSUME TRUE PROVE FALSE
     OBVIOUS
   <2> QED
     BY <1>2 DEFS INC, TypeOK1
<1> QED
    BY <1>1, <1>2 DEFS INC
    
    
    
--------------------------------------------------------------------------
THEOREM Invariant == Spec => []Inv


--------------------------------------------------------------------------
THEOREM Consistent == Spec => []Consistency
<1> USE DEF Ballot
<1>1. Inv => Consistency
  <2> SUFFICES ASSUME Inv, 
                      NEW b1 \in Ballot, NEW b2 \in Ballot,
                      NEW v1 \in Value, NEW v2 \in Value,
                      ChosenIn(b1, v1), ChosenIn(b2, v2),
                      b1 <= b2
               PROVE v1 = v2
      BY DEFS Chosen, Consistency
  <2>1. CASE b1 = b2
    BY <2>1, VotedOnce, QuorumAssumption DEFS Inv, ChosenIn
  <2>2. CASE b1 < b2
    <3>1. SafeAt(b2, v2)
      BY VotedInv, QuorumAssumption DEFS ChosenIn, Inv
    <3>2. PICK Q2 \in Quorum:
        \A a \in Q2: VotedForIn(a, b1, v2) \/ WontVoteIn(a, b1)
      BY <2>2, <3>1 DEFS SafeAt
    <3>3. PICK Q1 \in Quorum:
        \A a \in Q1: VotedForIn(a, b1, v1)
      BY DEF ChosenIn
    <3>4. QED
      BY <3>3, <3>2, QuorumAssumption, VotedOnce DEFS WontVoteIn, Inv
  <2> QED 
    BY <2>1, <2>2
<1>2. QED
  BY Invariant, PTL, <1>1
---------------------------------------------------------------------------
(*
For checking Liveness
WF(A): if A ever becomes enabled, then an A step will eventually occur-even 
if A remains enabled for only a fraction of a nanosecond and is never again
enabled. 
Liveness in TPaxos: like paxos, there should be a single-leader to prapre
and accept.
*)

LConstrain == /\ \E p \in Participant:
                /\ MaxBallot \in Bals(p)
                /\ WF_vars(Prepare(p, MaxBallot))
                /\ \A v \in Value: WF_vars(Accept(p, MaxBallot, v))
                /\ \E Q \in Quorum:
                    /\ p \in Q
                    /\ \A q \in Q: WF_vars(OnMessage(q))

LSpec == Spec /\ LConstrain

Liveness == <>(chosen # {})
=============================================================================
\* Modification History
\* Last modified Sat Oct 10 11:09:04 CST 2020 by pure_
\* Last modified Fri Oct 09 14:33:01 CST 2020 by admin
\* Created Thu Jun 25 14:23:28 CST 2020 by admin