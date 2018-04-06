---------------------------- MODULE BlockchainMC ----------------------------

EXTENDS
    Naturals,
    Sequences,
    FiniteSets

CONSTANTS
    CalculateHash(_,_,_),
    MaxHashCount,
    PrivateKey,
    PublicKey,
    Node,
    Value

VARIABLES
    hashFunction,
    lastHash,
    createdBlocks,
    confirmedBlocks,
    top

ASSUME
    /\ Cardinality(PrivateKey) = Cardinality(PublicKey)
    /\ Cardinality(PublicKey) <= Cardinality(Node)

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

KeyPair ==
    [private : PrivateKey,
    public : PublicKey]

RECURSIVE AssociateKeyPairs(_,_)
AssociateKeyPairs(privateKeys, publicKeys) ==
    IF
        \/ privateKeys = {}
        \/ publicKeys = {}
    THEN {}
    ELSE
        LET pair ==
            [private |-> CHOOSE k \in privateKeys : TRUE,
            public |-> CHOOSE k \in publicKeys : TRUE]
        IN
        {pair} \cup
            AssociateKeyPairs(
                privateKeys \ {pair.private},
                publicKeys \ {pair.public})

AccountKeyPair ==
    AssociateKeyPairs(PrivateKey, PublicKey)

Ownership ==
    CHOOSE mapping \in [Node -> AccountKeyPair] :
        /\ \A pair \in AccountKeyPair :
            /\ \E node \in Node :
                /\ mapping[node] = pair

BC == INSTANCE Blockchain

TypeInvariant ==
    /\ hashFunction \in Seq(BC!Block)
    /\ BC!TypeInvariant

SafetyInvariant ==
    /\ \A hash \in Hash :
        LET signedBlock == confirmedBlocks[hash] IN
        /\ signedBlock /= BC!NoBlock =>
            LET blockHash == HashOf(signedBlock.block) IN
            /\ blockHash = hash
            /\ BC!ValidateSignature(
                signedBlock.signature,
                signedBlock.signer,
                blockHash)
    /\ BC!SafetyInvariant

Init ==
    /\ hashFunction = <<>>
    /\ BC!Init

StutterWhenHashesDepleted ==
    /\ UNCHANGED hashFunction
    /\ UNCHANGED lastHash
    /\ UNCHANGED createdBlocks
    /\ UNCHANGED confirmedBlocks
    /\ UNCHANGED top

Next ==
    IF UndefinedHashesExist
    THEN BC!Next
    ELSE StutterWhenHashesDepleted

=============================================================================