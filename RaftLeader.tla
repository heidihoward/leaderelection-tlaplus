---- MODULE RaftLeader ----

EXTENDS Integers

Server == {"s1", "s2", "s3"}
Quorum == {{"s1","s2"},{"s2","s3"},{"s1","s3"}}
MaxTerm == 4

Term == 0..MaxTerm

Message ==  
    [type : {"RequestVote"}, term : Term, from: Server]
    \cup [type : {"VoteGranted"}, from : Server, to: Server, term : Term]
    \cup [type : {"FollowMe"}, term : Term, from: Server]

VARIABLE 
    \* @type: Str -> Int;
    currentTerm,
     \* @type: Set([type: Str, term: Int, from: Str, to:Str]);
    messages

vars == <<currentTerm, messages>>

Init ==
    /\ currentTerm = [s \in Server |-> 0]
    /\ messages = {}

BecomeCandidate(s) ==
    /\ currentTerm[s] < MaxTerm
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ messages' = messages \union {[type |-> "RequestVote", term |-> currentTerm[s]+1, from |-> s]}

Vote(s) ==
    /\ \E m \in messages:
        /\ m.type = "RequestVote"
        /\ m.term > currentTerm[s]
        /\ currentTerm' = [currentTerm EXCEPT ![s] = m.term]
        /\ messages' = messages \union {[type |-> "VoteGranted", 
                                            term |-> m.term, from |-> s, to |-> m.from]}

BecomeLeader(s) ==
    /\ \E Q \in Quorum:
        \A s1 \in Q: 
            \E m \in messages: 
                /\ m.type = "VoteGranted"
                /\ m.term = currentTerm[s]
                /\ m.from = s1
                /\ m.to = s
    /\ messages' = messages \union {[type |-> "FollowMe", 
                                        term |-> currentTerm[s], from |-> s]}
    /\ UNCHANGED <<currentTerm>>

Noop ==
    /\ UNCHANGED <<currentTerm,messages>>    

Next ==
    \/ \E s \in Server:
        \/ BecomeCandidate(s)
        \/ Vote(s)
        \/ BecomeLeader(s)
        \/ Noop

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ currentTerm \in [Server -> Term]
    /\ messages \in SUBSET Message

OneVotePerTerm ==
    \A m1,m2 \in messages: \A s \in Server: 
       /\ m1.type = "VoteGranted" 
       /\ m2.type = "VoteGranted" 
       /\ m1.from = s 
       /\ m2.from = s 
       /\ m1.term = m2.term 
       => m1.to = m2.to

\* True if server s is a leader in term t
IsLeader(s,t) ==
    \E Q \in Quorum:
        \A s1 \in Q: 
            \E m \in messages: 
                /\ m.type = "VoteGranted"
                /\ m.term = t
                /\ m.from = s1
                /\ m.to = s

OneLeaderPerTerm ==
    \A t \in Term: 
        \A s1,s2 \in Server:
            /\ IsLeader(s1,t) 
            /\ IsLeader(s2,t) 
            => s1=s2

IncreasingTerms ==
    \A s \in Server, m \in messages: 
        m.from = s => currentTerm[s] \geq m.term

OnlyLeadersAppend ==
    \A m \in messages: m.type = "FollowMe" => IsLeader(m.from,m.term)

Safety ==
    \A t \in Term: 
        \A m1,m2 \in messages: 
            /\ m1.type = "FollowMe" 
            /\ m2.type = "FollowMe" 
            /\ m1.term = m2.term 
            => m1.from = m2.from 

Inv == 
    /\ TypeOK
    /\ IncreasingTerms
    /\ OneVotePerTerm
    /\ OneLeaderPerTerm
    /\ OnlyLeadersAppend
    /\ Safety

====