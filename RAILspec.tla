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
        print <<"start", c>>;
        w0: 
        while (logs # {}){
        
            sendline: 
            with (msg \in logs)
            {
                logs := logs \ { msg };
                print c;
                print msg;
                print logs;
            };   
        };
    
    };
    
    
};

*)


============== RAIL ===================

\* BEGIN TRANSLATION
VARIABLES servers, aggregators, clients, logs, ServerState, ServerQueue, 
          AggregatorState, AggregatorQueue, ClientTime, pc

vars == << servers, aggregators, clients, logs, ServerState, ServerQueue, 
           AggregatorState, AggregatorQueue, ClientTime, pc >>

ProcSet == (clients)

Init == (* Global variables *)
        /\ servers = 1..S
        /\ aggregators = 1..A
        /\ clients = 1..C
        /\ logs = { "Line0", "Line1", "Line2", "Line3" }
        /\ ServerState = [s \in servers |-> {}]
        /\ ServerQueue = [s \in servers |-> {}]
        /\ AggregatorState = [s \in aggregators |-> {}]
        /\ AggregatorQueue = [s \in servers |-> {}]
        /\ ClientTime = [s \in clients |-> 0]
        /\ pc = [self \in ProcSet |-> "wstart"]

wstart(self) == /\ pc[self] = "wstart"
                /\ PrintT(<<"start", c>>)
                /\ pc' = [pc EXCEPT ![self] = "w0"]
                /\ UNCHANGED << servers, aggregators, clients, logs, 
                                ServerState, ServerQueue, AggregatorState, 
                                AggregatorQueue, ClientTime >>

w0(self) == /\ pc[self] = "w0"
            /\ IF logs # {}
                  THEN /\ pc' = [pc EXCEPT ![self] = "sendline"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << servers, aggregators, clients, logs, ServerState, 
                            ServerQueue, AggregatorState, AggregatorQueue, 
                            ClientTime >>

sendline(self) == /\ pc[self] = "sendline"
                  /\ \E msg \in logs:
                       /\ logs' = logs \ { msg }
                       /\ PrintT(c)
                       /\ PrintT(msg)
                       /\ PrintT(logs')
                  /\ pc' = [pc EXCEPT ![self] = "w0"]
                  /\ UNCHANGED << servers, aggregators, clients, ServerState, 
                                  ServerQueue, AggregatorState, 
                                  AggregatorQueue, ClientTime >>

c(self) == wstart(self) \/ w0(self) \/ sendline(self)

Next == (\E self \in clients: c(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sat Oct 22 15:21:28 BST 2016 by george
\* Created Sat Oct 22 14:25:13 BST 2016 by george
