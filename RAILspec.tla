------------------------------ MODULE RAILspec ------------------------------
EXTENDS Naturals, TLC, FiniteSets, Sequences
CONSTANT S, A, C, K

(*

--fair algorithm RAIL {
  variables 

    servers = 1..S;
    aggregators = 1..A;
    clients = 1..C;
    
    subs = SUBSET servers;
    
    Quorums = {x \in subs : Cardinality(x) = K };
    
    \*logs = [c \in clients |-> {"Line0", "Line1", "Line2", "Line3" }];
    logs = [c \in clients |-> <<"Line0", "Line1", "Line2">> ];
 
    ServerState = [s \in servers |-> {}];
    ServerQueue = [s \in servers |-> {}];
    
    AggregatorState = [s \in aggregators |-> {}];
    AggregatorQueue = [s \in servers |-> {}];

    ClientTime = [s \in clients |-> 0];
    
    
    macro send(chan, msgs){
         chan := chan \cup { msgs };
    }
    
    
    process(c \in clients) 
        variable sentto = {};
        {      

        wstart:
        while (Len(logs[self]) # 0){
        
            winit: with (targets \in Quorums){
                sentto := targets;
            };
        
            sendloop:
            while(sentto # {}){
                with(chan \in sentto){
                    send( ServerQueue[chan] , { Head(logs[self]) });
                    sentto := sentto \ {chan}
                };                
            };
        
            logs[self] := Tail(logs[self]);
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
VARIABLES servers, aggregators, clients, subs, Quorums, logs, ServerState, 
          ServerQueue, AggregatorState, AggregatorQueue, ClientTime, pc, 
          sentto

vars == << servers, aggregators, clients, subs, Quorums, logs, ServerState, 
           ServerQueue, AggregatorState, AggregatorQueue, ClientTime, pc, 
           sentto >>

ProcSet == (clients) \cup (servers)

Init == (* Global variables *)
        /\ servers = 1..S
        /\ aggregators = 1..A
        /\ clients = 1..C
        /\ subs = SUBSET servers
        /\ Quorums = {x \in subs : Cardinality(x) = K }
        /\ logs = [c \in clients |-> <<"Line0", "Line1", "Line2">> ]
        /\ ServerState = [s \in servers |-> {}]
        /\ ServerQueue = [s \in servers |-> {}]
        /\ AggregatorState = [s \in aggregators |-> {}]
        /\ AggregatorQueue = [s \in servers |-> {}]
        /\ ClientTime = [s \in clients |-> 0]
        (* Process c *)
        /\ sentto = [self \in clients |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self \in clients -> "wstart"
                                        [] self \in servers -> "start"]

wstart(self) == /\ pc[self] = "wstart"
                /\ IF Len(logs[self]) # 0
                      THEN /\ pc' = [pc EXCEPT ![self] = "winit"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, 
                                logs, ServerState, ServerQueue, 
                                AggregatorState, AggregatorQueue, ClientTime, 
                                sentto >>

winit(self) == /\ pc[self] = "winit"
               /\ \E targets \in Quorums:
                    sentto' = [sentto EXCEPT ![self] = targets]
               /\ pc' = [pc EXCEPT ![self] = "sendloop"]
               /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, 
                               logs, ServerState, ServerQueue, AggregatorState, 
                               AggregatorQueue, ClientTime >>

sendloop(self) == /\ pc[self] = "sendloop"
                  /\ IF sentto[self] # {}
                        THEN /\ \E chan \in sentto[self]:
                                  /\ ServerQueue' = [ServerQueue EXCEPT ![chan] = (ServerQueue[chan]) \cup { ({ Head(logs[self]) }) }]
                                  /\ sentto' = [sentto EXCEPT ![self] = sentto[self] \ {chan}]
                             /\ pc' = [pc EXCEPT ![self] = "sendloop"]
                             /\ logs' = logs
                        ELSE /\ logs' = [logs EXCEPT ![self] = Tail(logs[self])]
                             /\ pc' = [pc EXCEPT ![self] = "wstart"]
                             /\ UNCHANGED << ServerQueue, sentto >>
                  /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, 
                                  ServerState, AggregatorState, 
                                  AggregatorQueue, ClientTime >>

c(self) == wstart(self) \/ winit(self) \/ sendloop(self)

start(self) == /\ pc[self] = "start"
               /\ ServerQueue[self] # {}
               /\ \E line \in ServerQueue[self]:
                    /\ ServerQueue' = [ServerQueue EXCEPT ![self] = ServerQueue[self] \ { line }]
                    /\ ServerState' = [ServerState EXCEPT ![self] = ServerState[self] \cup { line }]
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, 
                               logs, AggregatorState, AggregatorQueue, 
                               ClientTime, sentto >>

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
\* Last modified Sat Oct 22 17:42:07 BST 2016 by george
\* Last modified Sat Oct 22 16:30:04 BST 2016 by benl
\* Created Sat Oct 22 14:25:13 BST 2016 by george
