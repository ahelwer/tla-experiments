---------------------------- MODULE BlockchainMC ----------------------------

EXTENDS
    Naturals,
    Sequences

CONSTANTS
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

CalcHash(block) ==
    /\ UndefinedHashesExist
    /\ hashFunction' = Append(hashFunction, block)

GetHash(block) ==
    CHOOSE h \in DOMAIN hashFunction : hashFunction[h] = block

BC == INSTANCE Blockchain

TypeInvariant ==
    /\ hashFunction \in [Hash -> BC!Block \cup {BC!NoBlock}]
    /\ BC!TypeInvariant

SafetyInvariant ==
    /\ BC!SafetyInvariant

Init ==
    /\ hashFunction = [h \in Hash |-> BC!NoBlock]
    /\ BC!Init

Genesis(v) ==
    /\ UndefinedHashesExist
    /\ BC!Genesis(v)

CreateBlock(v) ==
    /\ BC!CreateBlock(v)

ConfirmBlock(v) ==
    /\ UndefinedHashesExist
    /\ BC!ConfirmBlock(v)

Next ==
    \/ \E v \in Value : Genesis(v)
    \/ \E v \in Value : CreateBlock(v)
    \/ \E v \in createdBlocks : ConfirmBlock(v)

=============================================================================