------------------------------- MODULE NanoMC -------------------------------

EXTENDS
    Naturals,
    Sequences

CONSTANTS
    CalculateHash(_,_,_),
    GenesisHash(_,_),
    HashOf(_),
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

CalculateHashImpl(block, oldLastHash, newLastHash) ==
    /\ UndefinedHashesExist
    /\ hashFunction' = Append(hashFunction, block)
    /\ newLastHash = Len(hashFunction')

HashOfImpl(block) ==
    CHOOSE h \in DOMAIN hashFunction : hashFunction[h] = block

GenesisHashImpl(genesisBlock, genesisHash) ==
    /\ hashFunction = <<genesisBlock>> 
    /\ genesisHash = HashOf(genesisBlock)

N == INSTANCE Nano

=============================================================================