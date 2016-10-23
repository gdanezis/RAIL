------------------------------ MODULE RAILspec ------------------------------
EXTENDS Naturals, TLC, FiniteSets, Sequences
CONSTANT S, A, C, K

(* Check if there is any client log left to send *)
SOMELEFT(client_states) == \E xy \in (DOMAIN client_states) : Len(client_states[xy]) > 0
SOMELEFTSET(client_states) == \E xy \in (DOMAIN client_states) : client_states[xy] # {}

(*

--fair algorithm RAIL {
  variables 

    servers = 1..S;
    aggregators = S+1..A+S;
    clients = A+S+1..A+S+C;
    
    subs = SUBSET servers;
    Quorums = {x \in subs : Cardinality(x) = K };
    
    asubs = SUBSET aggregators;
    AQuorums = {x \in asubs : Cardinality(x) = S - K + 1};
    
    \*logs = [c \in clients |-> {"Line0", "Line1", "Line2", "Line3" }];
    logs = [c \in clients |-> <<"Line0", "line1">> ];
 
    ServerState = [s \in servers |-> {}];
    ServerQueue = [s \in servers |-> <<>>];
    sr = [s \in servers |-> 1];
    
    AggregatorState = [s \in aggregators |-> {}];
    AggregatorQueue = [a \in aggregators |-> {}];

    ClientTime = [s \in clients |-> 0];
    
    
    macro send(chan, msgs){
         chan := chan \o msgs;
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
                    send( ServerQueue[chan] , << <<self, Head(logs[self])>> >>);
                    sentto := sentto \ {chan}
                };                
            };
        
            logs[self] := Tail(logs[self]);
        };                 
    };
    
    process(s \in servers)
    variable aa = {}; {
        w0:
        while(ServerQueue[self] # <<>> \/ SOMELEFT(logs)) {
            await ServerQueue[self] # <<>>;
            
            w2:
            with (targets \in AQuorums) {
                aa := targets;
            };
        
            w1:
            while (ServerQueue[self] # <<>>) {
                ServerState[self] := ServerState[self] \cup { Head(ServerQueue[self]) };
                w3:
                while (aa # {}) {
                    with (x \in aa) {
                        aa := aa \ { x };
                        AggregatorQueue[x] := AggregatorQueue[x] \cup { Head(ServerQueue[self]) };
                    }
                };
                ServerQueue[self] := Tail(ServerQueue[self]);
            }
        }
    }
    
    process(a \in aggregators)
    variable states = <<>>; {
        astart:
        while(AggregatorQueue[self] # {} \/ SOMELEFT(logs) \/ SOMELEFT(ServerQueue)) {
            with (m \in AggregatorQueue[self]) {
                AggregatorQueue[self] := AggregatorQueue[self] \ { m };       
                AggregatorState[self] := AggregatorState[self] \cup { m };
            }
        };
        (* presumably there's some way to run this check only once instead of in every process *)
        a2:
        (* wait for the others to finish *)
        await ~SOMELEFTSET(AggregatorQueue);
        with (n \in DOMAIN AggregatorState) {
            assert AggregatorState[self] = AggregatorState[n];
        }
    }
};

*)


\* ================ BEGIN TRANSLATION ================ *\
VARIABLES servers, aggregators, clients, subs, Quorums, asubs, AQuorums, logs, 
          ServerState, ServerQueue, sr, AggregatorState, AggregatorQueue, 
          ClientTime, pc, sentto, aa, states

vars == << servers, aggregators, clients, subs, Quorums, asubs, AQuorums, 
           logs, ServerState, ServerQueue, sr, AggregatorState, 
           AggregatorQueue, ClientTime, pc, sentto, aa, states >>

ProcSet == (clients) \cup (servers) \cup (aggregators)

Init == (* Global variables *)
        /\ servers = 1..S
        /\ aggregators = S+1..A+S
        /\ clients = A+S+1..A+S+C
        /\ subs = SUBSET servers
        /\ Quorums = {x \in subs : Cardinality(x) = K }
        /\ asubs = SUBSET aggregators
        /\ AQuorums = {x \in asubs : Cardinality(x) = S - K + 1}
        /\ logs = [c \in clients |-> <<"Line0", "line1">> ]
        /\ ServerState = [s \in servers |-> {}]
        /\ ServerQueue = [s \in servers |-> <<>>]
        /\ sr = [s \in servers |-> 1]
        /\ AggregatorState = [s \in aggregators |-> {}]
        /\ AggregatorQueue = [a \in aggregators |-> {}]
        /\ ClientTime = [s \in clients |-> 0]
        (* Process c *)
        /\ sentto = [self \in clients |-> {}]
        (* Process s *)
        /\ aa = [self \in servers |-> {}]
        (* Process a *)
        /\ states = [self \in aggregators |-> <<>>]
        /\ pc = [self \in ProcSet |-> CASE self \in clients -> "wstart"
                                        [] self \in servers -> "w0"
                                        [] self \in aggregators -> "astart"]

wstart(self) == /\ pc[self] = "wstart"
                /\ IF Len(logs[self]) # 0
                      THEN /\ pc' = [pc EXCEPT ![self] = "winit"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, 
                                asubs, AQuorums, logs, ServerState, 
                                ServerQueue, sr, AggregatorState, 
                                AggregatorQueue, ClientTime, sentto, aa, 
                                states >>

winit(self) == /\ pc[self] = "winit"
               /\ \E targets \in Quorums:
                    sentto' = [sentto EXCEPT ![self] = targets]
               /\ pc' = [pc EXCEPT ![self] = "sendloop"]
               /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, 
                               asubs, AQuorums, logs, ServerState, ServerQueue, 
                               sr, AggregatorState, AggregatorQueue, 
                               ClientTime, aa, states >>

sendloop(self) == /\ pc[self] = "sendloop"
                  /\ IF sentto[self] # {}
                        THEN /\ \E chan \in sentto[self]:
                                  /\ ServerQueue' = [ServerQueue EXCEPT ![chan] = (ServerQueue[chan]) \o (<< <<self, Head(logs[self])>> >>)]
                                  /\ sentto' = [sentto EXCEPT ![self] = sentto[self] \ {chan}]
                             /\ pc' = [pc EXCEPT ![self] = "sendloop"]
                             /\ logs' = logs
                        ELSE /\ logs' = [logs EXCEPT ![self] = Tail(logs[self])]
                             /\ pc' = [pc EXCEPT ![self] = "wstart"]
                             /\ UNCHANGED << ServerQueue, sentto >>
                  /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, 
                                  asubs, AQuorums, ServerState, sr, 
                                  AggregatorState, AggregatorQueue, ClientTime, 
                                  aa, states >>

c(self) == wstart(self) \/ winit(self) \/ sendloop(self)

w0(self) == /\ pc[self] = "w0"
            /\ IF ServerQueue[self] # <<>> \/ SOMELEFT(logs)
                  THEN /\ ServerQueue[self] # <<>>
                       /\ pc' = [pc EXCEPT ![self] = "w2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, 
                            asubs, AQuorums, logs, ServerState, ServerQueue, 
                            sr, AggregatorState, AggregatorQueue, ClientTime, 
                            sentto, aa, states >>

w2(self) == /\ pc[self] = "w2"
            /\ \E targets \in AQuorums:
                 aa' = [aa EXCEPT ![self] = targets]
            /\ pc' = [pc EXCEPT ![self] = "w1"]
            /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, 
                            asubs, AQuorums, logs, ServerState, ServerQueue, 
                            sr, AggregatorState, AggregatorQueue, ClientTime, 
                            sentto, states >>

w1(self) == /\ pc[self] = "w1"
            /\ IF ServerQueue[self] # <<>>
                  THEN /\ ServerState' = [ServerState EXCEPT ![self] = ServerState[self] \cup { Head(ServerQueue[self]) }]
                       /\ pc' = [pc EXCEPT ![self] = "w3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "w0"]
                       /\ UNCHANGED ServerState
            /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, 
                            asubs, AQuorums, logs, ServerQueue, sr, 
                            AggregatorState, AggregatorQueue, ClientTime, 
                            sentto, aa, states >>

w3(self) == /\ pc[self] = "w3"
            /\ IF aa[self] # {}
                  THEN /\ \E x \in aa[self]:
                            /\ aa' = [aa EXCEPT ![self] = aa[self] \ { x }]
                            /\ AggregatorQueue' = [AggregatorQueue EXCEPT ![x] = AggregatorQueue[x] \cup { Head(ServerQueue[self]) }]
                       /\ pc' = [pc EXCEPT ![self] = "w3"]
                       /\ UNCHANGED ServerQueue
                  ELSE /\ ServerQueue' = [ServerQueue EXCEPT ![self] = Tail(ServerQueue[self])]
                       /\ pc' = [pc EXCEPT ![self] = "w1"]
                       /\ UNCHANGED << AggregatorQueue, aa >>
            /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, 
                            asubs, AQuorums, logs, ServerState, sr, 
                            AggregatorState, ClientTime, sentto, states >>

s(self) == w0(self) \/ w2(self) \/ w1(self) \/ w3(self)

astart(self) == /\ pc[self] = "astart"
                /\ IF AggregatorQueue[self] # {} \/ SOMELEFT(logs) \/ SOMELEFT(ServerQueue)
                      THEN /\ \E m \in AggregatorQueue[self]:
                                /\ AggregatorQueue' = [AggregatorQueue EXCEPT ![self] = AggregatorQueue[self] \ { m }]
                                /\ AggregatorState' = [AggregatorState EXCEPT ![self] = AggregatorState[self] \cup { m }]
                           /\ pc' = [pc EXCEPT ![self] = "astart"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "a2"]
                           /\ UNCHANGED << AggregatorState, AggregatorQueue >>
                /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, 
                                asubs, AQuorums, logs, ServerState, 
                                ServerQueue, sr, ClientTime, sentto, aa, 
                                states >>

a2(self) == /\ pc[self] = "a2"
            /\ ~SOMELEFTSET(AggregatorQueue)
            /\ \E n \in DOMAIN AggregatorState:
                 Assert(AggregatorState[self] = AggregatorState[n], 
                        "Failure of assertion at line 105, column 13.")
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, 
                            asubs, AQuorums, logs, ServerState, ServerQueue, 
                            sr, AggregatorState, AggregatorQueue, ClientTime, 
                            sentto, aa, states >>

a(self) == astart(self) \/ a2(self)

Next == (\E self \in clients: c(self))
           \/ (\E self \in servers: s(self))
           \/ (\E self \in aggregators: a(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sun Oct 23 14:53:49 BST 2016 by benl
<<<<<<< HEAD
\* Last modified Sat Oct 22 18:05:41 BST 2016 by george
=======
\* Last modified Sat Oct 22 18:28:31 BST 2016 by george
\* Last modified Sat Oct 22 18:00:44 BST 2016 by benl
>>>>>>> refs/remotes/origin/master
\* Created Sat Oct 22 14:25:13 BST 2016 by george
