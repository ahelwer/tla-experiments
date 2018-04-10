------------------------- MODULE NanoMCExistential -------------------------

EXTENDS
    Naturals,
    Sequences

CONSTANTS
    CalculateHash(_,_,_),
    Hash,
    PrivateKey,
    PublicKey,
    Node,
    GenesisBalance

VARIABLES
    hashFunction,
    lastHash,
    distributedLedger,
    received

-----------------------------------------------------------------------------

KeyPair ==
    CHOOSE mapping \in [PrivateKey -> PublicKey] :
        /\ \A publicKey \in PublicKey :
            /\ \E privateKey \in PrivateKey :
                /\ mapping[privateKey] = publicKey

Ownership ==
    CHOOSE mapping \in [Node -> PrivateKey] :
        /\ \A privateKey \in PrivateKey :
            /\ \E node \in Node :
                /\ mapping[node] = privateKey

N == INSTANCE Nano

CalculateHashImpl(block, oldLastHash, newLastHash) ==
    IF hashFunction[block] /= N!NoHash
    THEN
        /\ newLastHash = hashFunction[block]
        /\ UNCHANGED hashFunction
    ELSE
        /\ \E hash \in Hash :
            /\ \A otherBlock \in N!Block :
                /\ hashFunction[otherBlock] /= hash
            /\ hashFunction' = [hashFunction EXCEPT ![block] = hash]
            /\ newLastHash = hash

TypeInvariant ==
    /\ hashFunction \in [N!Block -> Hash \cup {N!NoHash}]
    /\ N!TypeInvariant

SafetyInvariant ==
    /\ N!SafetyInvariant

Init ==
    /\ hashFunction = [block \in N!Block |-> N!NoHash]
    /\ N!Init

StutterWhenHashesDepleted ==
    /\ UNCHANGED hashFunction
    /\ UNCHANGED lastHash
    /\ UNCHANGED distributedLedger
    /\ UNCHANGED received

Next ==
    N!Next

=============================================================================