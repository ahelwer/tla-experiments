----------------------------- MODULE Blockchain -----------------------------
CONSTANTS
    Hash,
    CalculateHash(_,_,_),
    PrivateKey,
    PublicKey,
    AccountKeyPair,
    Node,
    Ownership,
    Value

VARIABLES
    lastHash,
    createdBlocks,
    confirmedBlocks,
    top

ASSUME
    /\ \A block, oldHash, newHash :
        /\ CalculateHash(block, oldHash, newHash) \in BOOLEAN
    /\ AccountKeyPair \in [private : PrivateKey, public : PublicKey]
    /\ Ownership \in [Node -> AccountKeyPair]

-----------------------------------------------------------------------------

(***************************************************************************)
(* Defines the set of valid blocks.                                        *)
(***************************************************************************)

GenesisBlock ==
    [value      : Value]

TransactionBlock ==
    [previous   : Hash,
    value       : Value]

Block ==
    GenesisBlock
    \cup TransactionBlock

Signature ==
    [data       : Hash,
    signedWith  : PrivateKey]

SignedBlock ==
    [block      : Block,
    signature   : Signature,
    signer      : PublicKey]

NoBlock == CHOOSE b : b \notin SignedBlock

NoHash == CHOOSE h : h \notin Hash

SignHash(hash, privateKey) ==
    [data |-> hash,
    signedWith |-> privateKey]

ValidateSignature(signature, publicKey, expectedHash) ==
    LET keyPair ==
        CHOOSE pair \in AccountKeyPair :
            /\ pair.public = publicKey
    IN
    /\ signature.signedWith = keyPair.private
    /\ signature.data = expectedHash

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ createdBlocks \subseteq SignedBlock
    /\ confirmedBlocks \in [Hash -> SignedBlock \cup {NoBlock}]
    /\ top \in Hash \cup {NoHash}

RECURSIVE ChainContainsCycles(_,_)
ChainContainsCycles(hash, discovered) ==
    LET signedBlock == confirmedBlocks[hash] IN
    LET block == signedBlock.block IN
    IF hash \in discovered
    THEN TRUE
    ELSE
        IF block \in GenesisBlock
        THEN FALSE
        ELSE ChainContainsCycles(block.previous, discovered \cup {hash})

RECURSIVE BlocksInChain(_)
BlocksInChain(hash) ==
    LET signedBlock == confirmedBlocks[hash] IN
    LET block == signedBlock.block IN
    IF block \in GenesisBlock
    THEN {hash}
    ELSE {hash} \cup BlocksInChain(block.previous)

SafetyInvariant ==
    /\ top /= NoHash =>
        LET blocksInChain == BlocksInChain(top) IN
        /\ ~ChainContainsCycles(top, {})
        /\ \A hash \in Hash :
            /\ confirmedBlocks[hash] /= NoBlock =>
                /\ hash \in blocksInChain

Init ==
    /\ lastHash = NoHash
    /\ createdBlocks = {}
    /\ confirmedBlocks = [h \in Hash |-> NoBlock]
    /\ top = NoHash

Genesis(node, genesisValue) ==
    LET genesisBlock == [value |-> genesisValue] IN
    LET keyPair == Ownership[node] IN
    /\ top = NoHash
    /\ CalculateHash(genesisBlock, lastHash, lastHash')
    /\ confirmedBlocks' =
        [confirmedBlocks EXCEPT
            ![lastHash'] =
                [block      |-> genesisBlock,
                signature   |-> SignHash(lastHash', keyPair.private),
                signer      |-> keyPair.public]]
    /\ top' = lastHash'
    /\ UNCHANGED createdBlocks

CreateBlock(node, blockValue) ==
    LET newBlock == [previous |-> top, value |-> blockValue] IN
    LET keyPair == Ownership[node] IN
    /\ top /= NoHash
    /\ CalculateHash(newBlock, lastHash, lastHash')
    /\ createdBlocks' =
        createdBlocks \cup
            {[block     |-> newBlock,
            signature   |-> SignHash(lastHash', keyPair.private),
            signer      |-> keyPair.public]}
    /\ UNCHANGED <<confirmedBlocks, top>>

ConfirmBlock(signedBlock) ==
    LET block == signedBlock.block IN
    /\ block.previous = top
    /\ CalculateHash(block, lastHash, lastHash')
    /\ ValidateSignature(
        signedBlock.signature,
        signedBlock.signer,
        lastHash')
    /\ confirmedBlocks' =
        [confirmedBlocks EXCEPT
            ![lastHash'] = signedBlock]
    /\ top' = lastHash'
    /\ createdBlocks' = {}

Next ==
    \/ \E n \in Node : \E v \in Value : Genesis(n, v)
    \/ \E n \in Node : \E v \in Value : CreateBlock(n, v)
    \/ \E b \in createdBlocks : ConfirmBlock(b)

=============================================================================