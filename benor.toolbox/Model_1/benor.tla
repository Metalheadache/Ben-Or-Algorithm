------------------------------- MODULE benor -------------------------------
EXTENDS Integers, FiniteSets
CONSTANTS N, F, MAXROUND, INPUT

Procs == 1..N

(* 
--algorithm benor 
{
    variable p1Msg={}, 
             p2Msg={}, 
             decided=[i \in Procs |-> -1];
    
    define
    {
        Select(mb,self,k,n) == {i \in 0..1 : Cardinality({msg \in mb : msg.nodeid = self 
                                            /\ msg.round = k /\ msg.value[1] = i}) > n}
    }
   
    fair process (p \in Procs) 
      variable x = INPUT[self], k = 0;
      {
          A: while ( k < MAXROUND ) 
          {
               k := k + 1;
               p1Msg := p1Msg \union {[nodeid |-> dest, round |-> k, value |-> <<self,x>>] : dest \in Procs};
               
               P1: await(Cardinality({msg \in p1Msg : msg.nodeid = self /\ msg.round = k}) >= (N - F));
                   p2Msg := p2Msg \union {[nodeid |-> dest, round |-> k, value |-> <<self,v>>] : dest \in Procs, 
                                           v \in IF Cardinality(Select(p1Msg,self,k,N \div 2)) > 0 
                                                 THEN Select(p1Msg,self,k,N \div 2) ELSE {-1}};
    
               P2: await(Cardinality({msg \in p2Msg : msg.nodeid = self /\ msg.round = k}) >= (N - F));
                   if (Cardinality(Select(p2Msg,self,k,F)) > 0) 
                   {
                      decided[self] := CHOOSE i \in Select(p2Msg,self,k,F) : TRUE
                   }
                   else
                   {
                     if (Cardinality(Select(p2Msg,self,k,0)) > 0)
                     {
                        x := CHOOSE i \in Select(p2Msg,self,k,0) : TRUE
                     }
                     else
                     {
                        x := 0 \* CHOOSE i \in 0..1 : TRUE
                     }
                   }
          }
    }
}
*)
\* BEGIN TRANSLATION
VARIABLES p1Msg, p2Msg, decided, pc

(* define statement *)
Select(mb,self,k,n) == {i \in 0..1 : Cardinality({msg \in mb : msg.nodeid = self
                                    /\ msg.round = k /\ msg.value[1] = i}) > n}

VARIABLES x, k

vars == << p1Msg, p2Msg, decided, pc, x, k >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ p1Msg = {}
        /\ p2Msg = {}
        /\ decided = [i \in Procs |-> -1]
        (* Process p *)
        /\ x = [self \in Procs |-> INPUT[self]]
        /\ k = [self \in Procs |-> 0]
        /\ pc = [self \in ProcSet |-> "A"]

A(self) == /\ pc[self] = "A"
           /\ IF k[self] < MAXROUND
                 THEN /\ k' = [k EXCEPT ![self] = k[self] + 1]
                      /\ p1Msg' = (p1Msg \union {[nodeid |-> dest, round |-> k'[self], value |-> <<self,x[self]>>] : dest \in Procs})
                      /\ pc' = [pc EXCEPT ![self] = "P1"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << p1Msg, k >>
           /\ UNCHANGED << p2Msg, decided, x >>

P1(self) == /\ pc[self] = "P1"
            /\ (Cardinality({msg \in p1Msg : msg.nodeid = self /\ msg.round = k[self]}) >= (N - F))
            /\ p2Msg' = (p2Msg \union {[nodeid |-> dest, round |-> k[self], value |-> <<self,v>>] : dest \in Procs,
                                        v \in IF Cardinality(Select(p1Msg,self,k[self],N \div 2)) > 0
                                              THEN Select(p1Msg,self,k[self],N \div 2) ELSE {-1}})
            /\ pc' = [pc EXCEPT ![self] = "P2"]
            /\ UNCHANGED << p1Msg, decided, x, k >>

P2(self) == /\ pc[self] = "P2"
            /\ (Cardinality({msg \in p2Msg : msg.nodeid = self /\ msg.round = k[self]}) >= (N - F))
            /\ IF Cardinality(Select(p2Msg,self,k[self],F)) > 0
                  THEN /\ decided' = [decided EXCEPT ![self] = CHOOSE i \in Select(p2Msg,self,k[self],F) : TRUE]
                       /\ x' = x
                  ELSE /\ IF Cardinality(Select(p2Msg,self,k[self],0)) > 0
                             THEN /\ x' = [x EXCEPT ![self] = CHOOSE i \in Select(p2Msg,self,k[self],0) : TRUE]
                             ELSE /\ x' = [x EXCEPT ![self] = CHOOSE i \in 0..1 : TRUE]
                       /\ UNCHANGED decided
            /\ pc' = [pc EXCEPT ![self] = "A"]
            /\ UNCHANGED << p1Msg, p2Msg, k >>

p(self) == A(self) \/ P1(self) \/ P2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Procs: p(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(p(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

BaitProgress == ~(<>(Termination /\ \A i \in Procs: ~(decided[i] = -1)))
Agreement == \A i,j \in Procs: (decided[i] = -1) \/ (decided[j] = -1) \/ decided[i] = decided[j]
MajorityReport == \A i \in Procs: ~decided[i] = 0
==================================================================
Termination: TRUE

BaitProgress: FALSE

Agreement: TRUE

MajorityReport: TRUE when F = 0
                FALSE when F = 1 and F = 2

MinorityReport (by testing MajorityReport): FALSE when F = 0
                                            TRUE when F = 1 and F = 2
