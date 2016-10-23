------------------------------ MODULE RAILspec ------------------------------
EXTENDS Naturals, TLC, FiniteSets, Sequences
CONSTANT S, A, C, K

(* Check if there is any client log left to send *)
SOMELEFT(client_states) == \E xy \in (DOMAIN client_states) : Len(client_states[xy]) > 0
SOMELEFTSET(client_states) == \E xy \in (DOMAIN client_states) : client_states[xy] # {}
ONESET(states) == \E x \in (DOMAIN states) : states[x] > 0
(*

--fair algorithm RAIL {
  variables
    servers = 1..S;
    aggregators = S+1..A+S;
    clients = A+S+1..A+S+C;

    subs = SUBSET servers;
    Quorums = { x \in subs : Cardinality(x) = K };

    AQuorums = { x \in subs : Cardinality(x) = S - K + 1 };
    \*AQuorums = { x \in subs : Cardinality(x) = S - K };

    \*logs = [ c \in clients |-> {"Line0", "Line1", "Line2", "Line3" } ];
    logs = [ c \in clients |-> << "Line0", "Line1" >> ];

    ServerState = [ s \in servers |-> {} ];
    ServerQueue = [ s \in servers |-> <<>> ];

    AggregatorState = [ s \in aggregators |-> {} ];
    ARunning = [ a \in aggregators |-> 1 ];

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

            w1:
            while (ServerQueue[self] # <<>>) {
                ServerState[self] := ServerState[self] \cup { Head(ServerQueue[self]) };
                ServerQueue[self] := Tail(ServerQueue[self]);
            }
        }
    }

    process(a \in aggregators)
    variable states = <<>>; ss = {}; {
        astart:
        await ~(SOMELEFT(logs) \/ SOMELEFT(ServerQueue));
        with (sss \in AQuorums) {
            ss := sss;
        };
        a1:
        while (ss # {}) {
            with (sss \in ss) {
                AggregatorState[self] := AggregatorState[self] \cup ServerState[sss];
                ss := ss \ { sss };
            }
        };
        ARunning[self] := 0;
        (* presumably there's some way to run this check only once instead of in every process *)
        a2:
        (* wait for the others to finish *)
        await ~ONESET(ARunning);
        states := DOMAIN AggregatorState;
        a3:
        while (states # {}) {
            with (n \in states) {
                assert AggregatorState[self] = AggregatorState[n];
                states := states \ { n };
            };
        }
    }
};

*)


\* ================ BEGIN TRANSLATION ================ *\
VARIABLES servers, aggregators, clients, subs, Quorums, AQuorums, logs, 
          ServerState, ServerQueue, AggregatorState, ARunning, ClientTime, pc, 
          sentto, aa, states, ss

vars == << servers, aggregators, clients, subs, Quorums, AQuorums, logs, 
           ServerState, ServerQueue, AggregatorState, ARunning, ClientTime, 
           pc, sentto, aa, states, ss >>

ProcSet == (clients) \cup (servers) \cup (aggregators)

Init == (* Global variables *)
        /\ servers = 1..S
        /\ aggregators = S+1..A+S
        /\ clients = A+S+1..A+S+C
        /\ subs = SUBSET servers
        /\ Quorums = { x \in subs : Cardinality(x) = K }
        /\ AQuorums = { x \in subs : Cardinality(x) = S - K + 1 }
        /\ logs = [ c \in clients |-> << "Line0", "Line1" >> ]
        /\ ServerState = [ s \in servers |-> {} ]
        /\ ServerQueue = [ s \in servers |-> <<>> ]
        /\ AggregatorState = [ s \in aggregators |-> {} ]
        /\ ARunning = [ a \in aggregators |-> 1 ]
        /\ ClientTime = [ s \in clients |-> 0 ]
        (* Process c *)
        /\ sentto = [self \in clients |-> {}]
        (* Process s *)
        /\ aa = [self \in servers |-> {}]
        (* Process a *)
        /\ states = [self \in aggregators |-> <<>>]
        /\ ss = [self \in aggregators |-> {}]
        /\ pc = [self \in ProcSet |-> CASE self \in clients -> "wstart"
                                        [] self \in servers -> "w0"
                                        [] self \in aggregators -> "astart"]

wstart(self) == /\ pc[self] = "wstart"
                /\ IF Len(logs[self]) # 0
                      THEN /\ pc' = [pc EXCEPT ![self] = "winit"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, 
                                AQuorums, logs, ServerState, ServerQueue, 
                                AggregatorState, ARunning, ClientTime, sentto, 
                                aa, states, ss >>

winit(self) == /\ pc[self] = "winit"
               /\ \E targets \in Quorums:
                    sentto' = [sentto EXCEPT ![self] = targets]
               /\ pc' = [pc EXCEPT ![self] = "sendloop"]
               /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, 
                               AQuorums, logs, ServerState, ServerQueue, 
                               AggregatorState, ARunning, ClientTime, aa, 
                               states, ss >>

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
                                  AQuorums, ServerState, AggregatorState, 
                                  ARunning, ClientTime, aa, states, ss >>

c(self) == wstart(self) \/ winit(self) \/ sendloop(self)

w0(self) == /\ pc[self] = "w0"
            /\ IF ServerQueue[self] # <<>> \/ SOMELEFT(logs)
                  THEN /\ ServerQueue[self] # <<>>
                       /\ pc' = [pc EXCEPT ![self] = "w1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, 
                            AQuorums, logs, ServerState, ServerQueue, 
                            AggregatorState, ARunning, ClientTime, sentto, aa, 
                            states, ss >>

w1(self) == /\ pc[self] = "w1"
            /\ IF ServerQueue[self] # <<>>
                  THEN /\ ServerState' = [ServerState EXCEPT ![self] = ServerState[self] \cup { Head(ServerQueue[self]) }]
                       /\ ServerQueue' = [ServerQueue EXCEPT ![self] = Tail(ServerQueue[self])]
                       /\ pc' = [pc EXCEPT ![self] = "w1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "w0"]
                       /\ UNCHANGED << ServerState, ServerQueue >>
            /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, 
                            AQuorums, logs, AggregatorState, ARunning, 
                            ClientTime, sentto, aa, states, ss >>

s(self) == w0(self) \/ w1(self)

astart(self) == /\ pc[self] = "astart"
                /\ ~(SOMELEFT(logs) \/ SOMELEFT(ServerQueue))
                /\ \E sss \in AQuorums:
                     ss' = [ss EXCEPT ![self] = sss]
                /\ pc' = [pc EXCEPT ![self] = "a1"]
                /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, 
                                AQuorums, logs, ServerState, ServerQueue, 
                                AggregatorState, ARunning, ClientTime, sentto, 
                                aa, states >>

a1(self) == /\ pc[self] = "a1"
            /\ IF ss[self] # {}
                  THEN /\ \E sss \in ss[self]:
                            /\ AggregatorState' = [AggregatorState EXCEPT ![self] = AggregatorState[self] \cup ServerState[sss]]
                            /\ ss' = [ss EXCEPT ![self] = ss[self] \ { sss }]
                       /\ pc' = [pc EXCEPT ![self] = "a1"]
                       /\ UNCHANGED ARunning
                  ELSE /\ ARunning' = [ARunning EXCEPT ![self] = 0]
                       /\ pc' = [pc EXCEPT ![self] = "a2"]
                       /\ UNCHANGED << AggregatorState, ss >>
            /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, 
                            AQuorums, logs, ServerState, ServerQueue, 
                            ClientTime, sentto, aa, states >>

a2(self) == /\ pc[self] = "a2"
            /\ ~ONESET(ARunning)
            /\ states' = [states EXCEPT ![self] = DOMAIN AggregatorState]
            /\ pc' = [pc EXCEPT ![self] = "a3"]
            /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, 
                            AQuorums, logs, ServerState, ServerQueue, 
                            AggregatorState, ARunning, ClientTime, sentto, aa, 
                            ss >>

a3(self) == /\ pc[self] = "a3"
            /\ IF states[self] # {}
                  THEN /\ \E n \in states[self]:
                            /\ Assert(AggregatorState[self] = AggregatorState[n], 
                                      "Failure of assertion at line 98, column 17.")
                            /\ states' = [states EXCEPT ![self] = states[self] \ { n }]
                       /\ pc' = [pc EXCEPT ![self] = "a3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED states
            /\ UNCHANGED << servers, aggregators, clients, subs, Quorums, 
                            AQuorums, logs, ServerState, ServerQueue, 
                            AggregatorState, ARunning, ClientTime, sentto, aa, 
                            ss >>

a(self) == astart(self) \/ a1(self) \/ a2(self) \/ a3(self)

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
\* Last modified Sun Oct 23 22:10:09 BST 2016 by benl
<<<<<<< HEAD
\* Last modified Sat Oct 22 18:05:41 BST 2016 by george
=======
\* Last modified Sat Oct 22 18:28:31 BST 2016 by george
\* Last modified Sat Oct 22 18:00:44 BST 2016 by benl
>>>>>>> refs/remotes/origin/master
\* Created Sat Oct 22 14:25:13 BST 2016 by george
