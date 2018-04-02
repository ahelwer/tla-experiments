---------------------------- MODULE BlockchainMC ----------------------------

EXTENDS
    Naturals,
    Sequences

CONSTANTS
    CalculateHash(_,_,_),
    HashOf(_),
    MaxHashCount,
    Value

VARIABLES
    hashFunction,
    lastHash,
    createdBlocks,
    confirmedBlocks,
    top

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

BC == INSTANCE Blockchain

TypeInvariant ==
    /\ hashFunction \in Seq(BC!Block)
    /\ BC!TypeInvariant

ExtendedTypeInvariant ==
    /\ \A h \in Hash :
        LET block == confirmedBlocks[h] IN
        /\ block /= BC!NoBlock => h = HashOf(block)
    /\ top = BC!NoHash =>
        /\ \A h \in Hash :
            /\ createdBlocks = {}
            /\ confirmedBlocks[h] = BC!NoBlock

SafetyInvariant ==
    /\ BC!SafetyInvariant

Init ==
    /\ hashFunction = <<>>
    /\ BC!Init

Genesis(v) ==
    /\ UndefinedHashesExist
    /\ BC!Genesis(v)

CreateBlock(v) ==
    /\ BC!CreateBlock(v)
    /\ UNCHANGED hashFunction

ConfirmBlock(v) ==
    /\ UndefinedHashesExist
    /\ BC!ConfirmBlock(v)

Next ==
    \/ \E v \in Value : Genesis(v)
    \/ \E v \in Value : CreateBlock(v)
    \/ \E v \in createdBlocks : ConfirmBlock(v)

=============================================================================