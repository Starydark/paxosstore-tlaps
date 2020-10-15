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
AllBallot == Ballot \cup {-1}
AllValue == Value \cup {None}
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
\*    /\ \A p \in Participant: state[p] \in [Participant -> State]
\*    /\ \A p \in Participant, q \in Participant:
\*            /\ state[p][q].maxBal \in AllBallot
\*            /\ state[p][q].maxVBal \in AllBallot
\*            /\ state[p][q].maxVVal \in AllValue
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
       new_state_qq == [maxBal |-> maxB, 
                        maxVBal |-> (IF (maxB <= pp.maxVBal) 
                                        THEN pp.maxVBal 
                                        ELSE state[q][q].maxVBal), 
                        maxVVal |-> (IF (maxB <= pp.maxVBal)
                                        THEN pp.maxVVal
                                        ELSE state[q][q].maxVVal)]
       new_state_qp == [maxBal |->  Max(state[q][p].maxBal, pp.maxBal),
                        maxVBal |-> Max(state[q][p].maxVBal, pp.maxVBal),
                        maxVVal |-> (IF (state[q][p].maxVBal < pp.maxVBal)
                                        THEN pp.maxVVal
                                        ELSE state[q][p].maxVVal)]
    IN  state' = 
          [state EXCEPT
              ![q] = [ state[q] EXCEPT
                          ![q] = new_state_qq,
                          ![p] = new_state_qp
                      ] 
           ]
\*        [state EXCEPT 
\*            ![q] = [state[q] EXCEPT 
\*                       ![q] = [state[q][q] EXCEPT 
\*                                 !.maxBal = maxB, \* make promise first and then accept
\*                                 !.maxVBal = (IF (maxB <= pp.maxVBal)  \* accept
\*                                             THEN pp.maxVBal ELSE @), 
\*                                 !.maxVVal = (IF (maxB <= pp.maxVBal)  \* accept
\*                                             THEN pp.maxVVal ELSE @)
\*                                 !.maxVBal = IF 
\*                                                (
\*                                                state[q][q].maxBal <= pp.maxVBal 
\*                                                /\ pp.maxBal <= pp.maxVBal
\*                                                )
\*                                             THEN pp.maxVBal ELSE @,
\*                                 !.maxVVal = IF (
\*                                                state[q][q].maxBal <= pp.maxVBal 
\*                                                /\ pp.maxBal <= pp.maxVBal
\*                                                )
\*                                             THEN pp.maxVVal ELSE @
\*                               ],
\*                      ![p] = [state[q][p] EXCEPT 
\*                                !.maxBal = Max(@, pp.maxBal),
\*                                !.maxVBal = Max(@, pp.maxVBal),
\*                                !.maxVVal = (IF (state[q][p].maxVBal < pp.maxVBal)
\*                                            THEN pp.maxVVal ELSE @)
\*                              ]
\*                    ] 
\*         ]
\*    
    
\*                  ![q][p].maxBal = Max(@, pp.maxBal),
\*                  ![q][p].maxVBal = Max(@, pp.maxVBal),
\*                  ![q][p].maxVVal = IF state[q][p].maxVBal < pp.maxVBal 
\*                                    THEN pp.maxVVal ELSE @,
\*                  ![q][q].maxBal = maxB, \* make promise first and then accept
\*                  ![q][q].maxVBal = IF maxB <= pp.maxVBal  \* accept
\*                                    THEN pp.maxVBal ELSE @, 
\*                  ![q][q].maxVVal = IF maxB <= pp.maxVBal  \* accept
\*                                    THEN pp.maxVVal ELSE @]  
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
                 THEN msgs' = msgs \cup {nm}
                 ELSE UNCHANGED msgs
\*               THEN msgs' = (msgs \ {m}) \cup {qm, nm}
\*               ELSE msgs' = (msgs \ {m}) \cup {qm}
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
\*    /\ state' = [state EXCEPT ![p][p].maxVBal = b,
\*                              ![p][p].maxVVal = v]
    /\ state' = [state EXCEPT ![p] = [state[p] EXCEPT 
                                        ![p] = [state[p][p] EXCEPT !.maxVBal = b,
                                                                   !.maxVVal = v]]]
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
                    /\ state[a][a].maxBal > b

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

IfElse(a, b, c) == IF c < b THEN a ELSE b

VARIABLE if_, arrs


IFELSE(p, state1, state2) == 
    LET max == Max(state1.maxBal, state2.maxBal)
     IN if_' =  [if_ EXCEPT 
                            !.maxBal = IF max > if_.maxBal
                                       THEN @
                                       ELSE state1.maxBal,
                            !.maxVBal = IF max > if_.maxBal
                                       THEN @
                                       ELSE state1.maxVBal]

IFELSE1(p, q, state1, state2) == 
    LET max == Max(state1.maxBal, state2.maxBal)
     IN arrs' =  
        [arrs EXCEPT 
            ![p] = [arrs[p] EXCEPT 
                    ![p] = [arrs[p][p] EXCEPT
                            !.maxBal = IF max > if_.maxBal
                                       THEN arrs[p][p].maxBal
                                       ELSE state1.maxBal,
                            !.maxVBal = IF max > if_.maxBal
                                       THEN arrs[p][p].maxVBal
                                       ELSE state1.maxVBal
                           ]
                           ,
                   ![q] = [arrs[p][q] EXCEPT 
                            !.maxBal = IF max > if_.maxBal
                                       THEN arrs[p][q].maxBal
                                       ELSE state1.maxBal,
                            !.maxVBal = IF max > if_.maxBal
                                       THEN arrs[p][q].maxVBal
                                       ELSE state1.maxVBal
                          ]
                   ]
       ]
                                       
LEMMA ASSUME NEW s1 \in State, NEW s2 \in State, arrs \in [Participant -> [Participant -> State]],
             NEW p \in Participant, NEW q \in Participant, IFELSE1(p, q, s1, s2)
       PROVE arrs[p][q]'.maxVBal \in {arrs[p][q].maxVBal, s1.maxVBal}
BY DEFS IFELSE1, State, Max

LEMMA \A a, b, c \in AllBallot: IfElse(a, b, c) \in {a, b}
BY DEFS IfElse, AllBallot, Ballot

LEMMA MaxBigger == \A a \in Ballot \cup {-1}, b \in Ballot \cup {-1}: Max(a, b) >= a /\ Max(a, b) >= b
BY DEFS Ballot, Max

LEMMA MaxTypeOK == \A a \in AllBallot, b \in AllBallot: Max(a, b) \in {a, b}
BY DEFS AllBallot, Ballot, Max

LEMMA UpdateStateBiggerProperty ==
     ASSUME NEW q \in Participant, NEW p \in Participant, NEW pp \in State,
                UpdateState(q, p, pp), TypeOK
     PROVE  /\ state'[q][q].maxBal >= state[q][q].maxBal
            /\ state'[q][q].maxBal \in Ballot \cup {-1}
BY MaxBigger DEFS UpdateState, TypeOK, State, Max

LEMMA UpdateStateResultProperty ==
    ASSUME NEW q \in Participant, NEW p \in Participant, NEW pp \in State,
                UpdateState(q, p, pp), TypeOK
    PROVE   /\ state'[q][q].maxBal \in AllBallot
            /\ state'[q][q].maxVBal \in AllBallot
            /\ state'[q][q].maxVVal \in AllValue
            /\ state'[q][p].maxBal \in AllBallot
            /\ state'[q][p].maxVBal \in AllBallot
            /\ state'[q][p].maxVVal \in AllValue
<1>a. state'[q][q].maxBal = IF
                        state[q][q].maxBal
                        > pp.maxBal
                        THEN state[q][q].maxBal
                        ELSE pp.maxBal
  BY DEFS UpdateState, TypeOK, AllBallot, Ballot, AllValue, State, Max
<1>b. state'[q][q].maxVBal \in {pp.maxVBal, state[q][q].maxVBal}
  <2>a. CASE Max(state[q][q].maxBal, pp.maxBal) =< pp.maxVBal
    <3>a. (IF
            Max(state[q][q].maxBal,
                pp.maxBal)
            =< pp.maxVBal
            THEN pp.maxVBal
            ELSE state[q][q].maxVBal) = pp.maxVBal
      BY <2>a DEFS Max
    <3>c. state'[q][q].maxVBal = (IF
                                    Max(state[q][q].maxBal,
                                        pp.maxBal)
                                    =< pp.maxVBal
                                    THEN pp.maxVBal
                                    ELSE state[q][q].maxVBal)
      BY DEFS UpdateState, Max
    <3>b. state'[q][q].maxVBal = pp.maxVBal
    BY <2>a, <3>a, Z3 DEFS UpdateState
    <3> QED
  <2>b. CASE Max(state[q][q].maxBal, pp.maxBal) > pp.maxVBal
  <2> QED
    BY Z3, <2>a, <2>b DEFS UpdateState, TypeOK, AllBallot, Ballot, AllValue, State, Max
<1>c. state'[q][q].maxVVal = IF
                   (IF
                      state[q][q].maxBal
                      > pp.maxBal
                      THEN state[q][q].maxBal
                      ELSE pp.maxBal)
                   =< pp.maxVBal
                   THEN pp.maxVVal
                   ELSE state[q][q].maxVVal
  BY DEFS UpdateState, TypeOK, AllBallot, Ballot, AllValue, State, Max
<1>1. 
    /\ state'[q][q].maxBal \in {state[q][q].maxBal, pp.maxBal}
    /\ state'[q][q].maxVBal \in {state[q][q].maxVBal, pp.maxVBal}
    /\ state'[q][q].maxVVal \in {state[q][q].maxVVal, pp.maxVVal}
  BY DEFS UpdateState, TypeOK, AllBallot, Ballot, AllValue, State, Max
<1>2. /\ state'[q][p].maxBal \in {state[q][p].maxBal, pp.maxBal}
    /\ state'[q][p].maxVBal \in {state[q][p].maxVBal, pp.maxVBal}
    /\ state'[q][p].maxVVal \in {state[q][p].maxVVal, pp.maxVVal}
  BY DEFS UpdateState, TypeOK, AllBallot, Ballot, AllValue, State, Max
<1>3. /\ state[q][q].maxBal \in AllBallot
      /\ state[q][q].maxVBal \in AllBallot
      /\ state[q][q].maxVVal \in AllValue
      /\ state[q][p].maxBal \in AllBallot
      /\ state[q][p].maxVBal \in AllBallot
      /\ state[q][p].maxVVal \in AllValue
      /\ pp.maxBal \in AllBallot
      /\ pp.maxVBal \in AllBallot
      /\ pp.maxVVal \in AllValue
  BY DEFS TypeOK, AllBallot, Ballot, AllValue, State
<1> QED 
  BY <1>1, <1>2, <1>3 DEF UpdateStateResultProperty

LEMMA UpdateStateTypeOKProperty ==
     ASSUME NEW q \in Participant, NEW p \in Participant, NEW pp \in State,
                UpdateState(q, p, pp), TypeOK
     PROVE state' \in [Participant -> [Participant -> State]]
<1> USE DEFS AllBallot, Ballot, TypeOK, State, Message, AllValue
<1>1. state'[q][q].maxBal \in AllBallot /\ state'[q][q].maxVBal \in AllBallot 
        /\ state'[q][q].maxVVal \in AllValue
    BY UpdateStateResultProperty
<1>2. /\ state'[q][p].maxBal \in AllBallot
    /\ state'[q][p].maxVBal \in AllBallot
    /\ state'[q][p].maxVVal \in AllValue
    BY UpdateStateResultProperty
<1>3. state'[q][q] \in State 
  BY <1>1 DEFS UpdateState
<1>4. state[q][p].maxBal \in AllBallot /\ state[q][p].maxVBal \in AllBallot 
        /\ state[q][p].maxVVal \in AllValue /\ state[q][p] \in State
  OBVIOUS
<1>5. state'[q][p] \in State
  BY <1>2, <1>4 DEFS UpdateState
<1>6. state[q] \in [Participant -> State] /\ state[q][q] \in State /\ state[q][p] \in State
  OBVIOUS
<1>7. state'[q] \in [Participant -> State]
  BY <1>3, <1>5, <1>6 DEFS UpdateState
<1> QED
  BY <1>7 DEFS UpdateState



\* <1>q1_1. state'[q][q].maxBal = Max(state[q][q].maxBal, pp.maxBal)
\*   BY DEFS UpdateState
\* <1>q1_2. state[q][q].maxBal \in AllBallot /\ pp.maxBal \in AllBallot 
\*         /\ Max(state[q][q].maxBal, pp.maxBal) \in AllBallot
\*   BY MaxTypeOK
\* <1>q1_3. state'[q][q].maxBal \in AllBallot
\*   BY <1>q1_1, <1>q1_2 DEFS UpdateState
\* <1>q2_1. state'[q][q].maxVBal \in {pp.maxVBal, state[q][q].maxVBal}
\*         /\ state'[q][q].maxVVal \in {pp.maxVVal, state[q][q].maxVVal}
\*   <2>1. CASE Max(state[q][q].maxBal, pp.maxBal) =< pp.maxVBal
\*     <3>1. state'[q][q].maxVBal = pp.maxVBal 
\*       OMITTED 
\*     <3>2. state'[q][q].maxVVal = pp.maxVVal
\*       OMITTED
\*     <3> QED 
\*       BY <3>1, <3>2
\*   <2>2. CASE Max(state[q][q].maxBal, pp.maxBal) > pp.maxVBal
\*     <3>1. state'[q][q].maxVBal = state[q][q].maxVBal
\*       BY <2>2 DEFS UpdateState
\*     <3>2. state'[q][q].maxVVal = state[q][q].maxVVal
\*       OMITTED 
\*     <3> QED
\*       BY <3>1, <3>2
\*   <2> QED
\*     BY <2>1, <2>2, Z3 DEFS UpdateState, Max
\* <1>q2_2. state'[q][q].maxVBal \in AllBallot
\*   BY <1>q2_1 DEFS UpdateState
\* <1>. state'[q][p] \in State
\*   BY DEFS UpdateState, TypeOK, Max, State
\* <1>. state'[q][q] \in State
\*   BY MaxTypeOK DEFS UpdateState
\* <1>. state'[q] \in [Participant -> State]
\*   BY  DEFS UpdateState, TypeOK
\* <1> QED
\*   BY DEFS UpdateState, TypeOK

LEMMA OnMessageBiggerProperty ==
     ASSUME NEW q \in Participant, OnMessage(q), TypeOK
     PROVE  state'[q][q].maxBal >= state[q][q].maxBal
<1>1 PICK m \in msgs: OnMessage(q)!(m)
  BY DEFS OnMessage
<1>2. UpdateState(q, m.from, m.state[m.from])
  BY <1>1 DEFS OnMessage
<1> QED
  BY <1>2, UpdateStateBiggerProperty DEFS OnMessage, TypeOK, Message


LEMMA MsgNotLost == Next /\ TypeOK => 
        \A m \in msgs, b1 \in Ballot, p1 \in Participant, v1 \in Value: 
                       /\ m.from = p1
                       /\ m.state[p1].maxBal = b1
                       /\ m.state[p1].maxVBal = b1
                       /\ m.state[p1].maxVVal = v1
                       => m \in msgs'
<1> USE DEFS TypeOK, Ballot, State, Send
<1>1. ASSUME NEW pp \in Participant, NEW bb \in Ballot,
             Prepare(pp, bb), TypeOK
      PROVE \A m \in msgs: m \in msgs'
  BY <1>1 DEFS Prepare
<1>2. ASSUME NEW pp \in Participant, NEW bb \in Ballot, NEW vv \in Value,
             Accept(pp, bb, vv)
      PROVE \A m \in msgs: m \in msgs'
  BY <1>2 DEFS Accept
<1>3. ASSUME NEW pp \in Participant, OnMessage(pp), NEW m \in msgs,
             NEW b1 \in Ballot, NEW p1 \in Participant, NEW v1 \in Value,
             m.from = p1, m.state[p1].maxBal = b1, m.state[p1].maxVBal = b1,
             m.state[p1].maxVVal = v1
      PROVE m \in msgs'
  <2> PICK mm \in msgs: OnMessage(pp)!(mm)
    BY <1>3 DEFS OnMessage
  <2>1 CASE \/ mm.state[pp].maxBal < state'[pp][pp].maxBal
            \/ mm.state[pp].maxVBal < state'[pp][pp].maxVBal
   BY <2>1 DEFS OnMessage
  <2>2 CASE ~ (\/ mm.state[pp].maxBal < state'[pp][pp].maxBal
            \/ mm.state[pp].maxVBal < state'[pp][pp].maxVBal)
    BY <2>2 DEFS OnMessage
  <2> QED
    BY <1>3, <2>1, <2>2
<1> QED
  BY <1>1, <1>2, <1>3 DEFS Next

LEMMA RealBiggerThanView ==
    \A p \in Participant, q \in Participant:
        state[p][p].maxBal >= state[p][q].maxBal 



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
<1> USE DEFS Send, Ballot, TypeOK, State, AllBallot, AllValue
<1>1. ASSUME NEW pp \in Participant, NEW bb \in Ballot, Prepare(pp, bb), TypeOK
      PROVE SafeAt(b, v)'
\*      BY <1>1, QuorumAssumption DEFS Prepare, SafeAt, TypeOK, VotedForIn, WontVoteIn
  <2> DEFINE mm == [from |-> pp, to |-> Participant \ {pp}, state |-> state'[pp]]
  <2>1. \A p1 \in Participant, b1 \in Ballot, v1 \in Value:
        VotedForIn(p1, b1, v1) => VotedForIn(p1, b1, v1)'
    BY <1>1 DEFS VotedForIn, Prepare
  <2>2. \A p1 \in Participant, b1 \in Ballot:
        state[p1][p1].maxBal > b1 => state'[p1][p1].maxBal > b1
    BY <1>1 DEFS Prepare, Inv
  <2>3. \A p1 \in Participant, b1 \in Ballot, v1 \in Value:
        ~ VotedForIn(p1, b1, v1) => ~ VotedForIn(p1, b1, v1)'
    <3>1. mm \in msgs'
      BY <1>1 DEF Prepare
    <3>2. mm.state[pp].maxBal > mm.state[pp].maxVBal
      BY <1>1 DEF AccInv, Prepare, Inv
    <3> QED
      BY <1>1, <3>1, <3>2 DEFS Prepare, AccInv, VotedForIn, Inv
  <2>4. \A p1 \in Participant, b1 \in Ballot:
        WontVoteIn(p1, b1) => WontVoteIn(p1, b1)'
    BY <2>2, <2>3 DEFS Prepare, WontVoteIn
  <2>5. QED    
   BY <1>1, <2>1, <2>4, QuorumAssumption DEFS Prepare, SafeAt
<1>2. ASSUME NEW pp \in Participant, NEW bb \in Ballot, NEW vv \in Value,
             Accept(pp, bb, vv)
      PROVE SafeAt(b, v)'
  <2>1. \A p1 \in Participant, b1 \in Ballot, v1 \in Value:
        VotedForIn(p1, b1, v1) => VotedForIn(p1, b1, v1)'
    BY <1>2 DEFS VotedForIn, Accept
  <2>2. \A p1 \in Participant, b1 \in Ballot:
        state[p1][p1].maxBal > b1 => state'[p1][p1].maxBal > b1
    BY <1>2 DEFS Accept
  <2>3. ASSUME NEW p1 \in Participant, NEW b1 \in Ballot, NEW v1 \in Value,
               WontVoteIn(p1, b1), VotedForIn(p1, b1, v1)'
        PROVE FALSE
    <3> PICK mm \in msgs':/\ mm.from = p1
                          /\ mm.state[p1].maxBal = b1
                          /\ mm.state[p1].maxVBal = b1
                          /\ mm.state[p1].maxVVal = v1
      BY <2>3 DEFS VotedForIn
    <3>1. mm \in msgs'
      BY <2>3 DEFS VotedForIn
    <3>2. mm \notin msgs
      BY <2>3 DEFS WontVoteIn, VotedForIn
    <3>3. p1 = pp 
      BY <1>2, <3>1, <3>2 DEFS Accept
    <3>4. mm = [from |-> pp, to |-> Participant \ {pp},
                   state |-> (state')[pp]]
          /\ state'[pp][pp].maxVBal = bb
      BY <1>2, <3>1, <3>2 DEFS Accept
    <3>5. b1 = bb
      BY <1>2, <3>1, <3>2, <3>4 DEFS Accept, Inv
    <3> QED
      BY <1>2, <2>3, <3>3, <3>5 DEFS Accept, WontVoteIn, VotedForIn, Inv
  <2>4. \A p1 \in Participant, b1 \in Ballot:
        WontVoteIn(p1, b1) => WontVoteIn(p1, b1)'
    BY <1>2, <2>2, <2>3 DEFS Accept, WontVoteIn
  <2> QED
    BY <1>2, <2>1, <2>4, QuorumAssumption DEF Accept, SafeAt
<1>3. ASSUME NEW pp \in Participant, OnMessage(pp), TypeOK'
      PROVE SafeAt(b, v)'
  <2>1. \A p1 \in Participant, b1 \in Ballot, v1 \in Value:
        VotedForIn(p1, b1, v1) => VotedForIn(p1, b1, v1)'
\*    BY <1>3 DEFS VotedForIn, OnMessage, UpdateState, Max
   <3>1. SUFFICES ASSUME NEW p1 \in Participant, NEW b1 \in Ballot, 
                       NEW v1 \in Value, VotedForIn(p1, b1, v1)
                PROVE VotedForIn(p1, b1, v1)'
       OBVIOUS
   <3>2. PICK m \in msgs:
               /\ m.from = p1
               /\ m.state[p1].maxBal = b1
               /\ m.state[p1].maxVBal = b1
               /\ m.state[p1].maxVVal = v1
     BY <3>1 DEFS VotedForIn
   <3>3. m \in msgs'
     BY <1>3, <3>1, <3>2, MsgNotLost DEFS Inv
   <3> QED
     BY <3>1, <3>2, <3>3 DEFS VotedForIn
  <2>2. \A p1 \in Participant, b1 \in Ballot:
        state[p1][p1].maxBal > b1 => state'[p1][p1].maxBal > b1
    <3>1. SUFFICES ASSUME NEW p1 \in Participant, NEW b1 \in AllBallot,
                    state[p1][p1].maxBal > b1
                 PROVE state'[p1][p1].maxBal > b1
        OBVIOUS
    <3>2. PICK mm \in msgs: OnMessage(pp)!(mm)
      BY <1>3 DEFS OnMessage
    <3>3. CASE p1 = pp
      <4>3. state[pp][pp].maxBal \in AllBallot
        BY DEFS Inv
      <4>1. state'[pp][pp].maxBal \in AllBallot
        BY <1>3
      <4>2. state'[pp][pp].maxBal >= state[pp][pp].maxBal
        BY <1>3, OnMessageBiggerProperty DEFS Inv
      <4> QED
        BY <3>1, <3>3, <4>1, <4>2, <4>3 DEFS Inv
    <3>4. CASE p1 # pp
      BY <1>3, <3>1, <3>2, <3>4 DEFS UpdateState, Max, OnMessage
    <3> QED
        BY <3>1, <3>2, <3>3, <3>4
  <2>3. ASSUME NEW p1 \in Participant, NEW b1 \in AllBallot, NEW v1 \in Value,
               WontVoteIn(p1, b1), VotedForIn(p1, b1, v1)'
        PROVE FALSE
    <3>1. PICK mm \in msgs':/\ mm.from = p1
                            /\ mm.state[p1].maxBal = b1
                            /\ mm.state[p1].maxVBal = b1
                            /\ mm.state[p1].maxVVal =v1
      BY <2>3 DEFS VotedForIn
    <3>2. mm \notin msgs
      BY <2>3, <3>1 DEFS WontVoteIn, VotedForIn, Inv
    <3>3. CASE p1 = pp
      <4>1. state'[pp][pp].maxBal = b1
        BY <1>3, <2>3, <3>1, <3>2, <3>3 DEFS OnMessage
      <4>2. state[pp][pp].maxBal > b1
        BY <2>3, <3>1, <3>2, <3>3 DEFS VotedForIn, WontVoteIn
      <4>3. state'[pp][pp].maxBal >= state[pp][pp].maxBal
        BY <1>3, OnMessageBiggerProperty DEFS Inv
      <4>5. state[pp][pp].maxBal \in AllBallot
        BY DEFS Inv
      <4>6. state'[pp][pp].maxBal \in AllBallot
        BY <1>3
      <4>4. state'[pp][pp].maxBal > b1
        BY <4>2, <4>3, <4>5, <4>6
      <4> QED
        BY <4>1, <4>4
    <3>4. CASE p1 # pp
      BY <1>3, <3>1, <3>2, <3>4 DEFS OnMessage
    <3> QED
      BY <3>1, <3>2, <3>3, <3>4 DEFS OnMessage, WontVoteIn, VotedForIn, Inv
  <2>4. \A p1 \in Participant, b1 \in Ballot:
            WontVoteIn(p1, b1) => WontVoteIn(p1, b1)'
    BY <1>3, <2>2, <2>3 DEFS OnMessage, WontVoteIn
  <2> QED
    BY <1>3, <2>1, <2>4, QuorumAssumption DEFS OnMessage, SafeAt
<1> QED
  BY <1>1, <1>2, <1>3 DEF Next, Inv
   
    
VARIABLE inc, arr, triple, var
TypeOK1 == /\ inc \in Ballot \cup {-1}
           /\ var \in Ballot
           /\ arr \in [Nat -> [Nat -> State]]
           /\ triple \in [Participant -> State]
           
UpdateState2(q, p, pp) ==
    /\ LET maxB == Max(state[q][q].maxBal, pp.maxBal)
        IN  state' = [state EXCEPT 
\*                  ![q][p].maxBal = maxB,
\*                  ![q][p].maxVBal = maxB,
\*                  ![q][p].maxVVal = maxB,
                  ![q][q].maxBal = 0 \* make promise first and then accept
\*                  ![q][q].maxVBal = maxB, 
\*                  ![q][q].maxVVal = maxB
                 ]  

UpdateState3(q, p, pp) ==
    /\ LET maxB == Max(arr[q][q].maxBal, pp.maxBal)
        IN  arr' = [arr EXCEPT 
\*                  ![q][p].maxBal = maxB,
\*                  ![q][p].maxVBal = maxB,
\*                  ![q][p].maxVVal = maxB,
                  ![q][q].maxBal = maxB, \* make promise first and then accept
                  ![q][q].maxVBal = maxB, 
                  ![q][q].maxVVal = maxB,
\*                  ![q][q].maxVBal = maxB, 
                  ![q][q].maxVVal = maxB
                 ] 

UpdateState1(q, p, pp) == 
    LET maxB == Max(arr[q][q].maxBal, pp.maxBal)
    IN  arr' = [arr EXCEPT
                  ![q][p] = maxB, 
                  ![q][q].maxBal = maxB \* make promise first and then accept
                  ]

INC(p) ==
    \E b \in 3..5:
         LET max == Max(b, inc)
         IN  inc' = max

LEMMA ASSUME NEW b \in AllBallot, NEW p \in AllBallot, TypeOK1, 
             inc > b, inc' >= inc, inc' \in AllBallot
      PROVE  inc' > b

  BY DEFS TypeOK1, AllBallot


UpdateState4(p) ==
    state' = [state EXCEPT
                  ![p][p].maxBal = -1
                 ]
                 
Update(p) == triple' = [triple EXCEPT ![p].maxBal = -1]

LEMMA ASSUME NEW p \in Participant, TypeOK,
             Update(p)
       PROVE state'[p][p] \in State
<1> USE DEF TypeOK
<1>1. state'[p][p].maxBal \in Ballot \cup {-1}
  BY DEFS TypeOK, Ballot, State, Update, Message
<1>2. state'[p][p].maxVBal \in Ballot \cup {-1}
  BY DEFS TypeOK, Ballot, State, Update, Message
<1>3. state'[p][p].maxVVal \in Value \cup {None}
  BY DEFS TypeOK, Ballot, State, Update, Message
<1> QED
  BY <1>1, <1>2, <1>3 DEFS State, TypeOK, Update

LEMMA ASSUME NEW p \in Participant, TypeOK,
             UpdateState4(p)
       PROVE state'[p][p] \in State
<1>1. state'[p][p].maxBal \in Ballot \cup {-1}
  BY DEFS TypeOK, Ballot, State, UpdateState4, Message
<1>2. state'[p][p].maxVBal \in Ballot \cup {-1}
  BY DEFS TypeOK, Ballot, State, UpdateState4, Message
<1>3. state'[p][p].maxVVal \in Value \cup {None}
  BY DEFS TypeOK, Ballot, State, UpdateState4, Message
<1>4. state[p][p] \in State
<1> QED
  BY <1>1, <1>2, <1>3 DEFS State, TypeOK, UpdateState4

LEMMA ASSUME NEW p \in Participant, NEW q \in Participant, 
             NEW state_pp \in State, NEW b \in Ballot, TypeOK,
             state[p][p].maxBal > b, UpdateState2(p, q, state_pp),
             state'[p][p].maxBal > state[p][p].maxBal
      PROVE  state'[p][p].maxBal > b
  BY DEFS TypeOK, Ballot, State, UpdateState2

LEMMA 
    ASSUME NEW pp \in Nat, NEW qq \in Nat,
           NEW state_pp \in State,
            UpdateState3(pp, qq, state_pp), TypeOK1
           PROVE arr'[pp][pp].maxBal = 
                Max(arr[pp][pp].maxBal, state_pp.maxBal)
BY DEFS UpdateState3, TypeOK1, State

LEMMA INCAlways == 
        \E p \in Nat: INC(p) /\ TypeOK1 => 
        \A b1 \in Ballot: inc > b1 => inc' > b1    
<1> USE DEF Ballot, TypeOK1
<1>1. SUFFICES ASSUME NEW bb \in Ballot, NEW pp \in Participant,
                         INC(pp), TypeOK1, NEW b2 \in Ballot, inc > b2
              PROVE inc' > b2
  OBVIOUS
<1>2. inc' >= inc
  BY <1>1 DEFS INC, Max
<1> QED
  BY <1>1 DEFS INC
  
  

--------------------------------------------------------------------------
THEOREM Invariant == Spec => []Inv
<1> USE DEFS Send, Ballot, TypeOK, State, AllBallot, InitState, 
             AllValue, Message, vars
<1>1. Init => Inv
  BY DEFS Init, AccInv, InitState, VotedForIn, MsgInv, TypeOK, Inv
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars
                PROVE Inv'
      OBVIOUS
  <2> USE DEF Inv
  <2>1. CASE Next
    <3>1. TypeOK'
      <4>1. ASSUME NEW p \in Participant, NEW b \in Ballot, Prepare(p, b), Inv
             PROVE TypeOK'
        <5>1. state'[p][p].maxBal \in AllBallot
          BY <4>1 DEFS Prepare
        <5>2. state'[p][p].maxVBal \in AllBallot
          BY <4>1 DEFS Prepare
        <5>3. state'[p][p].maxVVal \in AllValue
          BY <4>1 DEFS Prepare
        <5>4. state'[p][p] \in State
          BY <4>1, <5>1, <5>2, <5>3 DEFS Prepare
        <5>5. state' \in [Participant -> [Participant -> State]]
          BY <4>1, <5>4 DEFS Prepare
        <5>6. [from |-> p, to |-> Participant \ {p},
                      state |-> (state')[p]] \in Message
          BY <5>5
        <5>7. msgs' \subseteq Message
          BY <4>1, <5>6 DEFS Prepare
        <5> QED
          BY <5>5, <5>7 DEFS Prepare
      <4>2. ASSUME NEW p \in Participant, NEW b \in Ballot, NEW v \in Value, Accept(p, b, v), Inv
             PROVE TypeOK'
        <5>1. state[p][p].maxBal >= b
          BY <4>2, RealBiggerThanView , QuorumAssumption DEFS AccInv, Accept
        <5>2. state[p][p].maxBal <= b
          BY <4>2, <5>1 DEFS Accept
        <5>3. state'[p][p].maxBal = b /\ state'[p][p].maxVBal = b /\ state'[p][p].maxVVal = v
          BY <4>2, <5>1, <5>2 DEFS Accept
        <5>5. state' \in [Participant -> [Participant -> State]]
          BY <4>2, <5>3 DEFS Accept
        <5>6. [from |-> p, to |-> Participant \ {p},
                      state |-> (state')[p]] \in Message
          BY <5>5
        <5>7. msgs' \subseteq Message
          BY <4>2, <5>6 DEFS Accept
        <5> QED
        BY <4>2, <5>6, <5>7 DEFS Accept
      <4>3. ASSUME NEW p \in Participant, OnMessage(p), Inv
             PROVE TypeOK'
        <5>1. PICK mm \in msgs: OnMessage(p)!(mm)
          BY <4>3 DEFS OnMessage
        <5>2. mm.state[mm.from] \in State
          BY <4>3, <5>1 DEFS OnMessage
        <5>3. state'[p][p] \in State
          BY <4>3 DEFS OnMessage, UpdateState
        <5> [from |-> p, to |-> {mm.from}, state |-> (state')[p]] \in Message
          BY <4>3 DEFS OnMessage, UpdateState
        <5> msgs' \subseteq Message
          BY <4>3 DEFS OnMessage, UpdateState, Max
        <5> QED
      <4> QED
        BY <2>1, <4>1, <4>2, <4>3 DEFS Next
    <3>2. MsgInv'
    <3>3. AccInv'
    <3> QED     
      BY <3>1, <3>2, <3>3 DEFS Inv
  <2>2. CASE UNCHANGED vars
    BY <2>2 DEFS AccInv, MsgInv, TypeOK, VotedForIn, Next,
            SafeAt, WontVoteIn, VotedForIn
  <2> QED
    BY <2>1, <2>2
<1> QED
  BY <1>1, <1>2, PTL DEFS Spec


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
\* Last modified Thu Oct 15 17:06:55 CST 2020 by stary
\* Last modified Wed Oct 14 16:39:25 CST 2020 by pure_
\* Last modified Fri Oct 09 14:33:01 CST 2020 by admin
\* Created Thu Jun 25 14:23:28 CST 2020 by admin