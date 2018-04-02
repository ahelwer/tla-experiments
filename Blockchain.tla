----------------------------- MODULE Blockchain -----------------------------
CONSTANTS
    Hash,
    CalcHash(_),
    GetHash(_),
    Value

VARIABLES
    createdBlocks,
    confirmedBlocks,
    top

-----------------------------------------------------------------------------

GenesisBlock ==
    [value : Value]

TransactionBlock ==
    [previous : Hash,
    value : Value]

Block == GenesisBlock \cup TransactionBlock

NoBlock == CHOOSE b : b \notin Block

HF ==
    INSTANCE HashFunctionInterface WITH
        Data <- Block

TypeInvariant ==
    /\ createdBlocks \subseteq Value
    /\ confirmedBlocks \in [Hash -> Block \cup {NoBlock}]
    /\ top \in Hash \cup {HF!NoHash}

RECURSIVE ChainContainsCycles(_,_)
ChainContainsCycles(hash, discovered) ==
    LET block == confirmedBlocks[hash] IN
    IF hash \in discovered
    THEN TRUE
    ELSE
        IF block \in GenesisBlock
        THEN FALSE
        ELSE ChainContainsCycles(block.previous, discovered \cup {hash})

RECURSIVE BlocksInChain(_)
BlocksInChain(hash) ==
    LET block == confirmedBlocks[hash] IN
    IF block \in GenesisBlock
    THEN {hash}
    ELSE {hash} \cup BlocksInChain(block.previous)

SafetyInvariant ==
    /\ ~ChainContainsCycles(top, {})
    /\ \A h \in Hash :
        LET blocksInChain == BlocksInChain(top) IN
        /\ confirmedBlocks[h] /= NoBlock <=> h \in blocksInChain

Init ==
    /\ createdBlocks = {}
    /\ confirmedBlocks = [h \in Hash |-> NoBlock]
    /\ top = HF!NoHash

Genesis(v) ==
    LET genesisBlock == [value |-> v] IN
    /\ CalcHash(genesisBlock)
    /\ top = HF!NoHash
    /\ confirmedBlocks' =
        [confirmedBlocks EXCEPT
            ![GetHash(genesisBlock)] = genesisBlock]
    /\ top' = GetHash(genesisBlock)

CreateBlock(v) ==
    /\ createdBlocks' = createdBlocks \cup {v}
    /\ UNCHANGED <<confirmedBlocks, top>>

ConfirmBlock(v) ==
    LET newBlock == [previous |-> top, value |-> v] IN
    /\ CalcHash(newBlock)
    /\ confirmedBlocks' =
        [confirmedBlocks EXCEPT
            ![GetHash(newBlock)] = newBlock]
    /\ createdBlocks' = createdBlocks \ {v}
    /\ top' = GetHash(newBlock)

Next ==
    \/ \E v \in Value : Genesis(v)
    \/ \E v \in Value : CreateBlock(v)
    \/ \E v \in createdBlocks : ConfirmBlock(v)

=============================================================================