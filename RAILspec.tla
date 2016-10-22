------------------------------ MODULE RAILspec ------------------------------
EXTENDS Naturals, TLC
CONSTANT S, A, C 

(*

--fair algorithm RAIL {
  variables 

    servers = 1..S;
    aggregators = 1..A;
    clients = 1..C;
    
    logs = { "Line0", "Line1", "Line2", "Line3" };
    logs2 = { "Line0", "Line1", "Line2", "Line3" };

    ServerState = [s \in servers |-> {}];
    ServerQueue = [s \in servers |-> {}];
    
    AggregatorState = [s \in aggregators |-> {}];
    AggregatorQueue = [s \in servers |-> {}];

    ClientTime = [s \in clients |-> 0];
    
    
    macro send(chan, msgs){
         chan := chan \cup msgs;
    }

    process(c \in clients){
        wstart:
        print <<"start">>;
        w0: 
        while (logs # {}){        
            sendline: 
            with (msg \in logs)
            {
                logs := logs \ { msg };
                with(s \in servers){
                    send(ServerQueue[s], { msg });
                };
            };   
        };                 
    };
    
    process(s \in servers){
        
        start: await ServerQueue[self] # {};
        with (line \in ServerQueue[self]){
            ServerQueue[self] := ServerQueue[self] \ { line };
            ServerState[self] := ServerState[self] \cup { line };
        }
        
    
    
    }
    
    
    
};

*)


\* ================ BEGIN TRANSLATION ================ *\
VARIABLES servers, aggregators, clients, logs, logs2, ServerState, 
          ServerQueue, AggregatorState, AggregatorQueue, ClientTime, pc

vars == << servers, aggregators, clients, logs, logs2, ServerState, 
           ServerQueue, AggregatorState, AggregatorQueue, ClientTime, pc >>

ProcSet == (clients) \cup (servers)

Init == (* Global variables *)
        /\ servers = 1..S
        /\ aggregators = 1..A
        /\ clients = 1..C
        /\ logs = { "Line0", "Line1", "Line2", "Line3" }
        /\ logs2 = { "Line0", "Line1", "Line2", "Line3" }
        /\ ServerState = [s \in servers |-> {}]
        /\ ServerQueue = [s \in servers |-> {}]
        /\ AggregatorState = [s \in aggregators |-> {}]
        /\ AggregatorQueue = [s \in servers |-> {}]
        /\ ClientTime = [s \in clients |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in clients -> "wstart"
                                        [] self \in servers -> "start"]

wstart(self) == /\ pc[self] = "wstart"
                /\ PrintT(<<"start">>)
                /\ pc' = [pc EXCEPT ![self] = "w0"]
                /\ UNCHANGED << servers, aggregators, clients, logs, logs2, 
                                ServerState, ServerQueue, AggregatorState, 
                                AggregatorQueue, ClientTime >>

w0(self) == /\ pc[self] = "w0"
            /\ IF logs # {}
                  THEN /\ pc' = [pc EXCEPT ![self] = "sendline"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << servers, aggregators, clients, logs, logs2, 
                            ServerState, ServerQueue, AggregatorState, 
                            AggregatorQueue, ClientTime >>

sendline(self) == /\ pc[self] = "sendline"
                  /\ \E msg \in logs:
                       /\ logs' = logs \ { msg }
                       /\ \E s \in servers:
                            ServerQueue' = [ServerQueue EXCEPT ![s] = (ServerQueue[s]) \cup ({ msg })]
                  /\ pc' = [pc EXCEPT ![self] = "w0"]
                  /\ UNCHANGED << servers, aggregators, clients, logs2, 
                                  ServerState, AggregatorState, 
                                  AggregatorQueue, ClientTime >>

c(self) == wstart(self) \/ w0(self) \/ sendline(self)

start(self) == /\ pc[self] = "start"
               /\ ServerQueue[self] # {}
               /\ \E line \in ServerQueue[self]:
                    /\ ServerQueue' = [ServerQueue EXCEPT ![self] = ServerQueue[self] \ { line }]
                    /\ ServerState' = [ServerState EXCEPT ![self] = ServerState[self] \cup { line }]
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << servers, aggregators, clients, logs, logs2, 
                               AggregatorState, AggregatorQueue, ClientTime >>

s(self) == start(self)

Next == (\E self \in clients: c(self))
           \/ (\E self \in servers: s(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sat Oct 22 16:12:21 BST 2016 by george
\* Created Sat Oct 22 14:25:13 BST 2016 by george
