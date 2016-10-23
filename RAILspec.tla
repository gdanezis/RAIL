------------------------------ MODULE RAILspec ------------------------------
EXTENDS Naturals, TLC, FiniteSets, Sequences
CONSTANT S, A, C, K

(* Check if there is any client log left to send *)
SOMELEFT(client_states) == \E xy \in (DOMAIN client_states) : Len(client_states[xy]) > 0
SOMELEFTSET(client_states) == \E xy \in (DOMAIN client_states) : client_states[xy] # {}

ALLAGGROSEQUAL(AggregatorState) == \A a1 \in (DOMAIN AggregatorState): \A a2 \in (DOMAIN AggregatorState): AggregatorState[a1] = AggregatorState[a2] 

(*

--fair algorithm RAIL {
  variables
    servers = 1..S;
    aggregators = S+1..A+S;
    clients = A+S+1..A+S+C;

    subs = SUBSET servers;
    Quorums = { x \in subs : Cardinality(x) = K };

    asubs = SUBSET aggregators;
    AQuorums = { x \in asubs : Cardinality(x) = S - K + 1 };

    \*logs = [ c \in clients |-> {"Line0", "Line1", "Line2", "Line3" } ];
    logs = [ c \in clients |-> <<"Line0">> ];

    ServerState = [ s \in servers |-> {} ];
    ServerQueue = [ s \in servers |-> <<>> ];

    AggregatorState = [ s \in aggregators |-> {} ];
    (* AggregatorQueue = [ a \in aggregators |-> {} ]; *)

    ClientTime = [ s \in clients |-> 0 ];

    macro send(chan, msgs){
         chan := chan \o msgs;
    }

    process(c \in clients)
        variable sentto = {}; {

        wstart:
        while (Len(logs[self]) # 0) {

        winit:
	    with (targets \in Quorums) {
                sentto := targets;
            };

            sendloop:
            while (sentto # {}) {
                 with (chan \in sentto) {               
                    send(ServerQueue[chan], << <<self, Head(logs[self])>> >>);
                    sentto := sentto \ {chan}
                 };
            };

            logs[self] := Tail(logs[self]);
        };
    };

    process(s \in servers)
    variable aa = {}; {
        w0:
        while (ServerQueue[self] # <<>> \/ SOMELEFT(logs)) {
            await ServerQueue[self] # <<>>;
                (* Since we do nothing in the future with this state -- do not keep it. *)
                ServerState[self] := ServerState[self] \cup { Head(ServerQueue[self]) };
                w2:
                with (targets \in AQuorums) {
                    aa := targets;
                };
                w3:
                while (aa # {}) {
                    with (x \in aa) {
                        aa := aa \ { x };
                        
                        (* Push directly to the aggregator state. *)
                        AggregatorState[x] := AggregatorState[x] \cup { Head(ServerQueue[self]) };
                        
                    };
                };
                ServerQueue[self] := Tail(ServerQueue[self]);
        }
    }

    process(a \in aggregators)
    {
        (* astart: *)
        (*
        while (AggregatorQueue[self] # {} \/ SOMELEFT(logs) \/ SOMELEFT(ServerQueue)) {
            with (m \in AggregatorQueue[self]) {
                AggregatorQueue[self] := AggregatorQueue[self] \ { m };
                AggregatorState[self] := AggregatorState[self] \cup { m };
            };
        };
        *)
        
        (* Since we take no action on receiving item place directly in State *)
        
        
        (* presumably there's some way to run this check only once instead of in every process *)
        
        (* wait for the others to finish *)
        (* await ~SOMELEFTSET(AggregatorQueue); *)
        (* a2: await ~SOMELEFT(logs) /\ ~SOMELEFT(ServerQueue); *)
        a2: await \A sxx \in servers: pc[sxx] = "Done";
        (* with (n \in DOMAIN AggregatorState) {
            print AggregatorState[self];
            print AggregatorState[n];
            assert AggregatorState[self] = AggregatorState[n]; *)
            assert ALLAGGROSEQUAL(AggregatorState);
        };
    }
};

*)


\* ================ BEGIN TRANSLATION ================ *\
VARIABLES servers, aggregators, clients, subs, Quorums, asubs, AQuorums, logs, 
          ServerState, ServerQueue, AggregatorState, ClientTime, pc, sentto, 
          aa

vars == << servers, aggregators, clients, subs, Quorums, asubs, AQuorums, 
           logs, ServerState, ServerQueue, AggregatorState, ClientTime, pc, 
           sentto, aa >>

ProcSet == (clients) \cup (servers) \cup (aggregators)

Init == (* Global variables *)
        /\ servers = 1..S
        /\ aggregators = S+1..A+S
        /\ clients = A+S+1..A+S+C
        /\ subs = SUBSET servers
        /\ Quorums = { x \in subs : Cardinality(x) = K }
        /\ asubs = SUBSET aggregators
        /\ AQuorums = { x \in asubs : Cardinality(x) = S - K + 1 }
        /\ logs = [ c \in clients |-> <<"Line0">> ]
        /\ ServerState = [ s \in servers |-> {} ]
        /\ ServerQueue = [ s \in servers |-> <<>> ]
        /\ AggregatorState = [ s \in aggregators |-> {} ]
        /\ ClientTime = [ s \in clients |-> 0 ]
        (* Process c *)
        /\ sentto = [self \in clients |-> {}]
        (* Process s *)
        /\ aa = [self \in servers |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self \in clients -> "wstart"
                                        [] self \in servers -> "w0"
                                        [] self \in aggregators -> "a2"]

wstart(self) == /\ pc[self] = "wstart"
                /\ IF Len(logs[self]) # 0
                      THEN /\ pc' = [pc EXCEPT ![self] = "winit"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, 
                                asubs, AQuorums, logs, ServerState, 
                                ServerQueue, AggregatorState, ClientTime, 
                                sentto, aa >>

winit(self) == /\ pc[self] = "winit"
               /\ \E targets \in Quorums:
                    sentto' = [sentto EXCEPT ![self] = targets]
               /\ pc' = [pc EXCEPT ![self] = "sendloop"]
               /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, 
                               asubs, AQuorums, logs, ServerState, ServerQueue, 
                               AggregatorState, ClientTime, aa >>

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
                                  asubs, AQuorums, ServerState, 
                                  AggregatorState, ClientTime, aa >>

c(self) == wstart(self) \/ winit(self) \/ sendloop(self)

w0(self) == /\ pc[self] = "w0"
            /\ IF ServerQueue[self] # <<>> \/ SOMELEFT(logs)
                  THEN /\ ServerQueue[self] # <<>>
                       /\ ServerState' = [ServerState EXCEPT ![self] = ServerState[self] \cup { Head(ServerQueue[self]) }]
                       /\ pc' = [pc EXCEPT ![self] = "w2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED ServerState
            /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, 
                            asubs, AQuorums, logs, ServerQueue, 
                            AggregatorState, ClientTime, sentto, aa >>

w2(self) == /\ pc[self] = "w2"
            /\ \E targets \in AQuorums:
                 aa' = [aa EXCEPT ![self] = targets]
            /\ pc' = [pc EXCEPT ![self] = "w3"]
            /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, 
                            asubs, AQuorums, logs, ServerState, ServerQueue, 
                            AggregatorState, ClientTime, sentto >>

w3(self) == /\ pc[self] = "w3"
            /\ IF aa[self] # {}
                  THEN /\ \E x \in aa[self]:
                            /\ aa' = [aa EXCEPT ![self] = aa[self] \ { x }]
                            /\ AggregatorState' = [AggregatorState EXCEPT ![x] = AggregatorState[x] \cup { Head(ServerQueue[self]) }]
                       /\ pc' = [pc EXCEPT ![self] = "w3"]
                       /\ UNCHANGED ServerQueue
                  ELSE /\ ServerQueue' = [ServerQueue EXCEPT ![self] = Tail(ServerQueue[self])]
                       /\ pc' = [pc EXCEPT ![self] = "w0"]
                       /\ UNCHANGED << AggregatorState, aa >>
            /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, 
                            asubs, AQuorums, logs, ServerState, ClientTime, 
                            sentto >>

s(self) == w0(self) \/ w2(self) \/ w3(self)

a2(self) == /\ pc[self] = "a2"
            /\ \A sxx \in servers: pc[sxx] = "Done"
            /\ Assert(ALLAGGROSEQUAL(AggregatorState), 
                      "Failure of assertion at line 113, column 13.")
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, 
                            asubs, AQuorums, logs, ServerState, ServerQueue, 
                            AggregatorState, ClientTime, sentto, aa >>

a(self) == a2(self)

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
\* Last modified Sun Oct 23 19:56:44 BST 2016 by george
\* Last modified Sun Oct 23 16:39:12 BST 2016 by benl
<<<<<<< HEAD
=======
\* Last modified Sat Oct 22 18:28:31 BST 2016 by george
\* Last modified Sat Oct 22 18:00:44 BST 2016 by benl
>>>>>>> refs/remotes/origin/master
\* Created Sat Oct 22 14:25:13 BST 2016 by george
