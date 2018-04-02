---------------------------- MODULE BlockchainMC ----------------------------

EXTENDS
    Naturals,
    Sequences

CONSTANTS
    CalcHash(_),
    GetHash(_),
    MaxHashCount,
    Value

VARIABLES
    hashFunction,
    createdBlocks,
    confirmedBlocks,
    top

-----------------------------------------------------------------------------

Hash == 1 .. MaxHashCount

UndefinedHashesExist ==
    Len(hashFunction) < MaxHashCount

CalcHashImpl(block) ==
    /\ UndefinedHashesExist
    /\ hashFunction' = Append(hashFunction, block)

GetHashImpl(block) ==
    CHOOSE h \in DOMAIN hashFunction' : hashFunction'[h] = block

BC == INSTANCE Blockchain

TypeInvariant ==
    /\ hashFunction \in Seq(BC!Block)
    /\ BC!TypeInvariant

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