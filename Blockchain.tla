----------------------------- MODULE Blockchain -----------------------------
CONSTANTS
    Hash,
    Value

VARIABLES
    HashFunction,
    CreatedBlocks,
    ConfirmedBlocks,
    Top

-----------------------------------------------------------------------------

NoHash == CHOOSE h : h \notin Hash

HashIsUndefined(h) ==
    /\ \A pair \in HashFunction :
        /\ pair[2] /= h

DefineHash(b, h) ==
    /\ HashFunction' = HashFunction \cup {<<b, h>>}

GenesisBlock ==
    [value : Value]

TransactionBlock ==
    [previous : Hash,
    value : Value]

Block == GenesisBlock \cup TransactionBlock

NoBlock == CHOOSE b : b \notin Block

TypeInvariant ==
    /\ HashGenerator \in Nat
    /\ HashFunction \subseteq Block \X Hash
    /\ CreatedBlocks \subseteq Value
    /\ ConfirmedBlocks \in [Hash -> Block \cup {NoBlock}]
    /\ Top \in Hash

RECURSIVE ChainContainsCycles(_,_)
ChainContainsCycles(hash, discovered) ==
    LET block == ConfirmedBlocks[hash] IN
    IF hash \in discovered
    THEN TRUE
    ELSE
        IF block \in GenesisBlock
        THEN FALSE
        ELSE ChainContainsCycles(block.previous, discovered \cup {hash})

RECURSIVE BlocksInChain(_)
BlocksInChain(hash) ==
    LET block == ConfirmedBlocks[hash] IN
    IF block \in GenesisBlock
    THEN {hash}
    ELSE {hash} \cup BlocksInChain(block.previous)

SafetyInvariant ==
    /\ ~ChainContainsCycles(Top, {})
    /\ \A h \in Hash :
        LET blocksInChain == BlocksInChain(Top) IN
        /\ ConfirmedBlocks[h] /= NoBlock <=> h \in blocksInChain

Init ==
    /\ \E v \in Value :
        LET genesisBlock == [value |-> v] IN
        /\ \E genesisHash \in Hash :
            /\ HashFunction = {<<genesisBlock, genesisHash>>}
            /\ ConfirmedBlocks =
                [h \in Hash |->
                    IF h = genesisHash
                    THEN genesisBlock
                    ELSE NoBlock]
            /\ Top = genesisHash
    /\ CreatedBlocks = {}

CreateBlock(v) ==
    /\ CreatedBlocks' = CreatedBlocks \cup {v}
    /\ UNCHANGED <<HashFunction, ConfirmedBlocks, Top>>

ConfirmBlock(v) ==
    LET newBlock == [previous |-> Top, value |-> v] IN
    /\ \E newHash \in Hash :
        /\ HashIsUndefined(newHash)
        /\ DefineHash(newBlock, newHash)
        /\ ConfirmedBlocks' =
            [ConfirmedBlocks EXCEPT
                ![newHash] = newBlock]
        /\ CreatedBlocks' = CreatedBlocks \ {v}
        /\ Top' = newHash

Next ==
    \/ \E v \in Value : CreateBlock(v)
    \/ \E v \in CreatedBlocks : ConfirmBlock(v)

=============================================================================