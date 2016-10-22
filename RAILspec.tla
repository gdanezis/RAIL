------------------------------ MODULE RAILspec ------------------------------
EXTENDS Naturals, TLC, FiniteSets, Sequences
CONSTANT S, A, C, K

(* Check if there is any client log left to send *)
SOMELEFT(client_states) == \E xy \in (DOMAIN client_states) : Len(client_states[xy]) > 0

(*

--fair algorithm RAIL {
  variables 

    servers = 1..S;
    aggregators = S+1..A+S;
    clients = A+S+1..A+S+C;
    
    subs = SUBSET servers;
    
    Quorums = {x \in subs : Cardinality(x) = K };
    
    \*logs = [c \in clients |-> {"Line0", "Line1", "Line2", "Line3" }];
    logs = [c \in clients |-> <<"Line0">> ];
 
    ServerState = [s \in servers |-> {}];
    ServerQueue = [s \in servers |-> {}];
    sr = [s \in servers |-> 1];
    
    AggregatorState = [s \in aggregators |-> {}];
    AggregatorQueue = [a \in aggregators |-> {}];

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
                    send( ServerQueue[chan] , { <<self, Head(logs[self])>> });
                    sentto := sentto \ {chan}
                };                
            };
        
            logs[self] := Tail(logs[self]);
        };                 
    };
    
    process(s \in servers)
    variable aa; {
        w0:
        while(ServerQueue[self] # {} \/ SOMELEFT(logs)) {
            await ServerQueue[self] # {};
            aa := aggregators;
            w1:
            with (line \in ServerQueue[self]){
                ServerQueue[self] := ServerQueue[self] \ { line };
                ServerState[self] := ServerState[self] \cup { line };
                with (x \in aa) {
                    aa := aa \ { x };
                    AggregatorQueue[x] := AggregatorQueue[x] \cup { line };
                }
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
        /\ logs = [c \in clients |-> <<"Line0">> ]
        /\ ServerState = [s \in servers |-> {}]
        /\ ServerQueue = [s \in servers |-> {}]
        /\ sr = [s \in servers |-> 1]
        /\ AggregatorState = [s \in aggregators |-> {}]
        /\ AggregatorQueue = [a \in aggregators |-> {}]
        /\ ClientTime = [s \in clients |-> 0]
        (* Process c *)
        /\ sentto = [self \in clients |-> {}]
        (* Process s *)
        /\ aa = [self \in servers |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> CASE self \in clients -> "wstart"
                                        [] self \in servers -> "w0"]

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
                                  /\ ServerQueue' = [ServerQueue EXCEPT ![chan] = (ServerQueue[chan]) \cup ({ <<self, Head(logs[self])>> })]
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

w0(self) == /\ pc[self] = "w0"
            /\ IF ServerQueue[self] # {} \/ SOMELEFT(logs)
                  THEN /\ ServerQueue[self] # {}
                       /\ aa' = [aa EXCEPT ![self] = aggregators]
                       /\ pc' = [pc EXCEPT ![self] = "w1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ aa' = aa
            /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, logs, 
                            ServerState, ServerQueue, sr, AggregatorState, 
                            AggregatorQueue, ClientTime, sentto >>

w1(self) == /\ pc[self] = "w1"
            /\ \E line \in ServerQueue[self]:
                 /\ ServerQueue' = [ServerQueue EXCEPT ![self] = ServerQueue[self] \ { line }]
                 /\ ServerState' = [ServerState EXCEPT ![self] = ServerState[self] \cup { line }]
                 /\ \E x \in aa[self]:
                      /\ aa' = [aa EXCEPT ![self] = aa[self] \ { x }]
                      /\ AggregatorQueue' = [AggregatorQueue EXCEPT ![x] = AggregatorQueue[x] \cup { line }]
            /\ pc' = [pc EXCEPT ![self] = "w0"]
            /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, logs, 
                            sr, AggregatorState, ClientTime, sentto >>

s(self) == w0(self) \/ w1(self)

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
\* Last modified Sat Oct 22 22:28:07 BST 2016 by benl
<<<<<<< HEAD
\* Last modified Sat Oct 22 18:05:41 BST 2016 by george
=======
\* Last modified Sat Oct 22 18:28:31 BST 2016 by george
\* Last modified Sat Oct 22 18:00:44 BST 2016 by benl
>>>>>>> refs/remotes/origin/master
\* Created Sat Oct 22 14:25:13 BST 2016 by george
