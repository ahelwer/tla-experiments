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
    privateKey,
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

N == INSTANCE Nano

TypeInvariant ==
    /\ hashFunction \in Seq(N!Block)
    /\ N!TypeInvariant

SafetyInvariant ==
    /\ N!SafetyInvariant

CreateGenesisBlock(genesisAccount) ==
    /\ UndefinedHashesExist
    /\ N!CreateGenesisBlock(genesisAccount)

CreateBlock(node) ==
    /\ N!CreateBlock(node)
    /\ UNCHANGED hashFunction

ProcessBlock(node) ==
    /\ UndefinedHashesExist
    /\ N!ProcessBlock(node)

Init ==
    /\ hashFunction = <<>>
    /\ N!Init

Next ==
    /\ UNCHANGED privateKey
    /\  \/ \E account \in Account : CreateGenesisBlock(account)
        \/ \E node \in Node : CreateBlock(node)
        \/ \E node \in Node : ProcessBlock(node)
        
=============================================================================