------------------------------ MODULE RAILspec ------------------------------
EXTENDS Naturals, TLC
CONSTANT S, A, C 

(*

--fair algorithm RAIL {
  variables 

    servers = 1..S;
    aggregators = 1..A;
    clients = 1..C;
    
    \*logs = [c \in clients |-> {"Line0", "Line1", "Line2", "Line3" }];
    logs = [c \in clients |-> {"Line0"}];
 
    ServerState = [s \in servers |-> {}];
    ServerQueue = [s \in servers |-> {}];
    
    AggregatorState = [s \in aggregators |-> {}];
    AggregatorQueue = [s \in servers |-> {}];

    ClientTime = [s \in clients |-> 0];
    
    
    macro send(chan, msgs){
         chan := chan \cup {msgs};
    }

    process(c \in clients){
        wstart:
        while (logs[self] # {}){
        
            sendline: 
            with (msg \in logs[self])
            {
                logs[self] := logs[self] \ { msg };
                with(s \in servers){
                    send(ServerQueue[s], msg);
                };
            };   
        };
                

    };
    
    
    
};

*)


\* ================ BEGIN TRANSLATION ================ *\
VARIABLES servers, aggregators, clients, logs, ServerState, ServerQueue, 
          AggregatorState, AggregatorQueue, ClientTime, pc

vars == << servers, aggregators, clients, logs, ServerState, ServerQueue, 
           AggregatorState, AggregatorQueue, ClientTime, pc >>

ProcSet == (clients)

Init == (* Global variables *)
        /\ servers = 1..S
        /\ aggregators = 1..A
        /\ clients = 1..C
        /\ logs = [c \in clients |-> {"Line0"}]
        /\ ServerState = [s \in servers |-> {}]
        /\ ServerQueue = [s \in servers |-> {}]
        /\ AggregatorState = [s \in aggregators |-> {}]
        /\ AggregatorQueue = [s \in servers |-> {}]
        /\ ClientTime = [s \in clients |-> 0]
        /\ pc = [self \in ProcSet |-> "wstart"]

wstart(self) == /\ pc[self] = "wstart"
                /\ IF logs[self] # {}
                      THEN /\ pc' = [pc EXCEPT ![self] = "sendline"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << servers, aggregators, clients, logs, 
                                ServerState, ServerQueue, AggregatorState, 
                                AggregatorQueue, ClientTime >>

sendline(self) == /\ pc[self] = "sendline"
                  /\ \E msg \in logs[self]:
                       /\ logs' = [logs EXCEPT ![self] = logs[self] \ { msg }]
                       /\ \E s \in servers:
                            ServerQueue' = [ServerQueue EXCEPT ![s] = (ServerQueue[s]) \cup {msg}]
                  /\ pc' = [pc EXCEPT ![self] = "wstart"]
                  /\ UNCHANGED << servers, aggregators, clients, ServerState, 
                                  AggregatorState, AggregatorQueue, ClientTime >>

c(self) == wstart(self) \/ sendline(self)

Next == (\E self \in clients: c(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sat Oct 22 16:13:49 BST 2016 by benl
\* Last modified Sat Oct 22 15:52:04 BST 2016 by george
\* Created Sat Oct 22 14:25:13 BST 2016 by george
