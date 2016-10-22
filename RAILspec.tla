------------------------------ MODULE RAILspec ------------------------------
EXTENDS Naturals, TLC, FiniteSets, Sequences
CONSTANT S, A, C, K

(*

--fair algorithm RAIL {
  variables 

    servers = 1..S;
    aggregators = S+1..A+S;
    clients = A+S+1..A+S+C;
    
    subs = SUBSET servers;
    
    Quorums = {x \in subs : Cardinality(x) = K };
    
    \*logs = [c \in clients |-> {"Line0", "Line1", "Line2", "Line3" }];
    logs = [c \in clients |-> <<"Line0", "Line1">> ];
 
    ServerState = [s \in servers |-> {}];
    ServerQueue = [s \in servers |-> {}];
    sr = [s \in servers |-> 1];
    
    AggregatorState = [s \in aggregators |-> {}];
    AggregatorQueue = [s \in servers |-> {}];

    ClientTime = [s \in clients |-> 0];
    
    
    macro send(chan, msgs){
         chan := chan \cup msgs;
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
    
    process(s \in servers)
    variable aa; {
        start:
        print <<"start">>;
        w0:
        while(sr[self] = 1) {
            await ServerQueue[self] # {};
            with (line \in ServerQueue[self]){
                ServerQueue[self] := ServerQueue[self] \ { line };
                ServerState[self] := ServerState[self] \cup { line };
                (*aa := {i \in aggregators};
                with (a \in aa) {
                    aa := aa \ { a };
                    AggregatorQueue[a] := AggregatorQueue[a] \cup { line };
                }*)
            }
        }
    }
    
    (*process(a \in aggregators) {
        start:
        while(1 = 1) {
            with (m \in AggregatorQueue[self]) {
                AggregatorQueue[self] := AggregatorQueue[self] \ { m };       
                AggregatorState[self] := AggregatorState[self] \cup { m };
            }
        }
    }*) 
};

*)


\* ================ BEGIN TRANSLATION ================ *\
CONSTANT defaultInitValue
VARIABLES servers, aggregators, clients, subs, Quorums, logs, ServerState, 
          ServerQueue, sr, AggregatorState, AggregatorQueue, ClientTime, pc, 
          sentto, aa

vars == << servers, aggregators, clients, subs, Quorums, logs, ServerState, 
           ServerQueue, sr, AggregatorState, AggregatorQueue, ClientTime, pc, 
           sentto, aa >>

ProcSet == (clients) \cup (servers)

Init == (* Global variables *)
        /\ servers = 1..S
        /\ aggregators = S+1..A+S
        /\ clients = A+S+1..A+S+C
        /\ subs = SUBSET servers
        /\ Quorums = {x \in subs : Cardinality(x) = K }
        /\ logs = [c \in clients |-> <<"Line0", "Line1">> ]
        /\ ServerState = [s \in servers |-> {}]
        /\ ServerQueue = [s \in servers |-> {}]
        /\ sr = [s \in servers |-> 1]
        /\ AggregatorState = [s \in aggregators |-> {}]
        /\ AggregatorQueue = [s \in servers |-> {}]
        /\ ClientTime = [s \in clients |-> 0]
        (* Process c *)
        /\ sentto = [self \in clients |-> {}]
        (* Process s *)
        /\ aa = [self \in servers |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self \in clients -> "wstart"
                                        [] self \in servers -> "start"]

wstart(self) == /\ pc[self] = "wstart"
                /\ IF Len(logs[self]) # 0
                      THEN /\ pc' = [pc EXCEPT ![self] = "winit"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, 
                                logs, ServerState, ServerQueue, sr, 
                                AggregatorState, AggregatorQueue, ClientTime, 
                                sentto, aa >>

winit(self) == /\ pc[self] = "winit"
               /\ \E targets \in Quorums:
                    sentto' = [sentto EXCEPT ![self] = targets]
               /\ pc' = [pc EXCEPT ![self] = "sendloop"]
               /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, 
                               logs, ServerState, ServerQueue, sr, 
                               AggregatorState, AggregatorQueue, ClientTime, 
                               aa >>

sendloop(self) == /\ pc[self] = "sendloop"
                  /\ IF sentto[self] # {}
                        THEN /\ \E chan \in sentto[self]:
                                  /\ ServerQueue' = [ServerQueue EXCEPT ![chan] = (ServerQueue[chan]) \cup ({ Head(logs[self]) })]
                                  /\ sentto' = [sentto EXCEPT ![self] = sentto[self] \ {chan}]
                             /\ pc' = [pc EXCEPT ![self] = "sendloop"]
                             /\ logs' = logs
                        ELSE /\ logs' = [logs EXCEPT ![self] = Tail(logs[self])]
                             /\ pc' = [pc EXCEPT ![self] = "wstart"]
                             /\ UNCHANGED << ServerQueue, sentto >>
                  /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, 
                                  ServerState, sr, AggregatorState, 
                                  AggregatorQueue, ClientTime, aa >>

c(self) == wstart(self) \/ winit(self) \/ sendloop(self)

start(self) == /\ pc[self] = "start"
               /\ PrintT(<<"start">>)
               /\ pc' = [pc EXCEPT ![self] = "w0"]
               /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, 
                               logs, ServerState, ServerQueue, sr, 
                               AggregatorState, AggregatorQueue, ClientTime, 
                               sentto, aa >>

w0(self) == /\ pc[self] = "w0"
            /\ IF sr[self] = 1
                  THEN /\ ServerQueue[self] # {}
                       /\ \E line \in ServerQueue[self]:
                            /\ ServerQueue' = [ServerQueue EXCEPT ![self] = ServerQueue[self] \ { line }]
                            /\ ServerState' = [ServerState EXCEPT ![self] = ServerState[self] \cup { line }]
                       /\ pc' = [pc EXCEPT ![self] = "w0"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << ServerState, ServerQueue >>
            /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, logs, 
                            sr, AggregatorState, AggregatorQueue, ClientTime, 
                            sentto, aa >>

s(self) == start(self) \/ w0(self)

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
\* Last modified Sat Oct 22 18:05:41 BST 2016 by george
\* Last modified Sat Oct 22 18:00:44 BST 2016 by benl
\* Created Sat Oct 22 14:25:13 BST 2016 by george
