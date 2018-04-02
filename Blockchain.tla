----------------------------- MODULE Blockchain -----------------------------
CONSTANTS
    Hash,
    CalculateHash(_,_,_),
    HashOf(_),
    Value

VARIABLES
    lastHash,
    createdBlocks,
    confirmedBlocks,
    top

-----------------------------------------------------------------------------

NoHash == CHOOSE h : h \notin Hash

GenesisBlock ==
    [value : Value]

TransactionBlock ==
    [previous : Hash,
    value : Value]

Block == GenesisBlock \cup TransactionBlock

NoBlock == CHOOSE b : b \notin Block

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ createdBlocks \subseteq Value
    /\ confirmedBlocks \in [Hash -> Block \cup {NoBlock}]
    /\ top \in Hash \cup {NoHash}

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
    /\ top /= NoHash =>
        /\ ~ChainContainsCycles(top, {})
        /\ \A h \in Hash :
            LET blocksInChain == BlocksInChain(top) IN
            /\ confirmedBlocks[h] /= NoBlock <=> h \in blocksInChain

Init ==
    /\ lastHash = NoHash
    /\ createdBlocks = {}
    /\ confirmedBlocks = [h \in Hash |-> NoBlock]
    /\ top = NoHash

Genesis(v) ==
    LET genesisBlock == [value |-> v] IN
    /\ top = NoHash
    /\ CalculateHash(genesisBlock, lastHash, lastHash')
    /\ confirmedBlocks' =
        [confirmedBlocks EXCEPT
            ![lastHash'] = genesisBlock]
    /\ top' = lastHash'
    /\ UNCHANGED createdBlocks

CreateBlock(v) ==
    /\ top /= NoHash
    /\ createdBlocks' = createdBlocks \cup {v}
    /\ UNCHANGED <<lastHash, confirmedBlocks, top>>

ConfirmBlock(v) ==
    LET newBlock == [previous |-> top, value |-> v] IN
    /\ top /= NoHash
    /\ CalculateHash(newBlock, lastHash, lastHash')
    /\ confirmedBlocks' =
        [confirmedBlocks EXCEPT
            ![lastHash'] = newBlock]
    /\ createdBlocks' = createdBlocks \ {v}
    /\ top' = lastHash'

Next ==
    \/ \E v \in Value : Genesis(v)
    \/ \E v \in Value : CreateBlock(v)
    \/ \E v \in createdBlocks : ConfirmBlock(v)

=============================================================================