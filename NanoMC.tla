------------------------------- MODULE NanoMC -------------------------------

EXTENDS
    Naturals,
    Sequences

CONSTANTS
    CalculateHash(_,_,_),
    Account,
    Node,
    MaxHashCount,
    GenesisBalance

VARIABLES
    hashFunction,
    lastHash,
    distributedLedger,
    received

-----------------------------------------------------------------------------

Hash == 1 .. MaxHashCount

UndefinedHashesExist ==
    Len(hashFunction) < MaxHashCount

HashIsDefined(block) ==
    /\ \E h \in DOMAIN hashFunction : hashFunction[h] = block

HashOf(block) ==
    CHOOSE h \in DOMAIN hashFunction : hashFunction[h] = block

CalculateHashImpl(block, oldLastHash, newLastHash) ==
    IF HashIsDefined(block)
    THEN
        /\ newLastHash = HashOf(block)
        /\ UNCHANGED hashFunction
    ELSE
        /\ UndefinedHashesExist
        /\ hashFunction' = Append(hashFunction, block)
        /\ newLastHash = Len(hashFunction')

PrivateKey ==
    CHOOSE ownership \in [Node -> Account] :
        /\ \A account \in Account :
            /\ \E node \in Node : ownership[node] = account

N == INSTANCE Nano

TypeInvariant ==
    /\ hashFunction \in Seq(N!Block)
    /\ N!TypeInvariant

SafetyInvariant ==
    /\ N!SafetyInvariant

Init ==
    /\ hashFunction = <<>>
    /\ N!Init

StutterWhenHashesDepleted ==
    /\ UNCHANGED hashFunction
    /\ UNCHANGED lastHash
    /\ UNCHANGED distributedLedger
    /\ UNCHANGED received

Next ==
    IF UndefinedHashesExist
    THEN N!Next
    ELSE StutterWhenHashesDepleted
        
=============================================================================