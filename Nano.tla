-------------------------------- MODULE Nano --------------------------------
EXTENDS
    Naturals

CONSTANTS
    Hash,
    CalculateHash(_,_,_),
    Account,
    Node,
    GenesisBalance,
    PrivateKey

VARIABLES
    lastHash,
    distributedLedger,
    received

ASSUME \A block, oldLastHash, newLastHash :
    CalculateHash(block, oldLastHash, newLastHash) \in BOOLEAN

ASSUME PrivateKey \in [Node -> Account]

-----------------------------------------------------------------------------

(***************************************************************************)
(* Defines the set of protocol-conforming blocks.                          *)
(***************************************************************************)

AccountBalance == 0 .. GenesisBalance

OpenBlock == [
    account : Account,
    source : Hash,
    representative : Account,
    type : {"open"},
    signature : Account]

SendBlock == [
    previous : Hash,
    balance : AccountBalance,
    destination : Account,
    type : {"send"},
    signature : Account]

ReceiveBlock == [
    previous : Hash,
    source : Hash,
    type : {"receive"},
    signature : Account]

ChangeRepBlock == [
    previous: Hash,
    representative : Account,
    type : {"change"},
    signature : Account]

GenesisBlock == [
    type : {"genesis"},
    account : Account,
    balance : {GenesisBalance},
    signature : Account]

Block ==
    OpenBlock
    \cup SendBlock
    \cup ReceiveBlock
    \cup ChangeRepBlock
    \cup GenesisBlock

NoBlock == CHOOSE b : b \notin Block

NoHash == CHOOSE h : h \notin Hash

Ledger == [Hash -> Block \cup {NoBlock}]

(***************************************************************************)
(* Utility functions to calculate block lattice properties.                *)
(***************************************************************************)

IsAccountOpen(ledger, account) ==
    /\ \A h \in Hash :
        LET block == ledger[h] IN
        /\ block /= NoBlock => block.signature /= account

IsSendReceived(ledger, sourceHash) ==
    /\ \E h \in Hash :
        LET block == ledger[h] IN
        /\ block /= NoBlock
        /\  \/ block.type = "open"
            \/ block.type = "receive"
        /\ block.source = sourceHash

RECURSIVE BalanceAt(_, _)
RECURSIVE ValueOfSendBlock(_, _)

BalanceAt(ledger, hash) ==
    LET block == ledger[hash] IN
    CASE block.type = "open" -> ValueOfSendBlock(ledger, block.source)
    [] block.type = "send" -> block.balance
    [] block.type = "receive" ->
        BalanceAt(ledger, block.previous)
        + ValueOfSendBlock(ledger, block.source)
    [] block.type = "change" -> BalanceAt(ledger, block.previous)
    [] block.type = "genesis" -> block.balance

ValueOfSendBlock(ledger, hash) ==
    LET block == ledger[hash] IN
    BalanceAt(ledger, block.previous) - block.balance
 
(***************************************************************************)
(* The type & safety invariants.                                           *)
(***************************************************************************)
TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in [Node -> Ledger]
    /\ PrivateKey \in [Node -> Account]
    /\ received \in [Node -> SUBSET Block]

SafetyInvariant == TRUE

(***************************************************************************)
(* Creates the genesis block under the specified account.                  *)
(***************************************************************************)
CreateGenesisBlock(genesisAccount) ==
    LET genesisBlock ==
        [type |-> "genesis",
        account |-> genesisAccount,
        balance |-> GenesisBalance,
        signature |-> genesisAccount]
    IN
    /\ lastHash = NoHash
    /\ CalculateHash(genesisBlock, lastHash, lastHash')
    /\ distributedLedger' =
        [n \in Node |->
            [distributedLedger[n] EXCEPT
                ![lastHash'] = genesisBlock]]
    /\ UNCHANGED received

(***************************************************************************)
(* Creation of an open block. This action allows Byzantine behaviour, with *)
(* the node specifying an arbitrary block in its possession as the source  *)
(* block. The node can also create an open block with an invalid signature *)
(* or create an open block for an account which has already been opened.   *)
(***************************************************************************)
CreateOpenBlock(node) ==
    /\ \E newAccount, repAccount \in Account :
        /\ \E srcHash \in Hash :
            LET newOpenBlock ==
                [account |-> newAccount,
                source |-> srcHash,
                representative |-> repAccount,
                type |-> "open",
                signature |-> PrivateKey[node]]
            IN
            /\ distributedLedger[node][srcHash] /= NoBlock
            /\ received' =
                [n \in Node |->
                    received[n] \cup {newOpenBlock}]
            /\ UNCHANGED <<distributedLedger, lastHash>>

(***************************************************************************)
(* A node validates an open block before confirming it. Checks include:    *)
(*  - The block is signed by the account being opened                      *)
(*  - The account is not already open                                      *)
(*  - The node's ledger contains the referenced source block               *)
(*  - The source block is a send block to the account being opened         *)
(***************************************************************************)
ProcessOpenBlock(node, block) ==
    LET ledger == distributedLedger[node] IN
    /\ block.type = "open"
    /\ block.signature = block.account
    /\ ~IsAccountOpen(ledger, block.account)
    /\ ledger[block.source] /= NoBlock
    /\ ledger[block.source].type = "send"
    /\ ledger[block.source].destination = block.account
    /\ CalculateHash(block, lastHash, lastHash')
    /\ distributedLedger' =
        [distributedLedger EXCEPT ![node] =
            [@ EXCEPT ![lastHash'] = block]]

(***************************************************************************)
(* Creation of a send block. This action allows Byzantine behaviour, with  *)
(* the node specifying an arbitrary block in its possession as the         *)
(* previous block. This can produce invalid transactions (which recipient  *)
(* nodes must catch), double spends, or normal valid transactions. An      *)
(* arbitrary amount of Nano is chosen as the value to send, which might be *)
(* more than the amount of Nano possessed by the account.                  *)
(***************************************************************************)
CreateSendBlock(node) ==
    /\ \E prevHash \in Hash :
        /\ \E dstAccount \in Account :
            /\ \E newBalance \in AccountBalance :
                LET newSendBlock ==
                    [previous |-> prevHash,
                    balance |-> newBalance,
                    destination |-> dstAccount,
                    type |-> "send",
                    signature |-> PrivateKey[node]]
                IN
                /\ distributedLedger[node][prevHash] /= NoBlock
                /\ received' =
                    [n \in Node |->
                        received[n] \cup {newSendBlock}]
                /\ UNCHANGED <<distributedLedger, lastHash>>

(***************************************************************************)
(* A node validates a send block before confirming it. Checks include:     *)
(*  - The node's ledger contains the referenced previous block             *)
(*  - The block is signed by the account sourcing the funds                *)
(*  - The value sent is non-negative                                       *)
(***************************************************************************)
ProcessSendBlock(node, block) ==
    LET ledger == distributedLedger[node] IN
    /\ block.type = "send"
    /\ ledger[block.previous] /= NoBlock
    /\ block.signature = ledger[block.previous].signature
    /\ block.balance <= BalanceAt(ledger, block.previous)
    /\ CalculateHash(block, lastHash, lastHash')
    /\ distributedLedger' =
        [distributedLedger EXCEPT ![node] =
            [@ EXCEPT ![lastHash'] = block]]

(***************************************************************************)
(* Creation of a receive block. This action allows Byzantine behaviour,    *)
(* with the node specifying arbitrary blocks in its possession as the      *)
(* previous and source blocks.                                             *)
(***************************************************************************)
CreateReceiveBlock(node) ==
    \E prevHash, srcHash \in Hash :
        LET newRcvBlock ==
            [previous |-> prevHash,
            source |-> srcHash,
            type |-> "receive",
            signature |-> PrivateKey[node]]
        IN
        /\ distributedLedger[node][prevHash] /= NoBlock
        /\ distributedLedger[node][srcHash] /= NoBlock
        /\ received' = [n \in Node |-> received[n] \cup {newRcvBlock}]
        /\ UNCHANGED <<distributedLedger, lastHash>>

(***************************************************************************)
(* A node validates a receive block before confirming it. Checks include:  *)
(*  - The node's ledger contains the referenced previous & source blocks   *)
(*  - The block is signed by the account sourcing the funds                *)
(*  - The source block is a send block to the receive block's account      *)
(*  - The source block does not already have a corresponding receive/open  *)
(***************************************************************************)
ProcessReceiveBlock(node, block) ==
    LET ledger == distributedLedger[node] IN
    /\ block.type = "receive"
    /\ ledger[block.previous] /= NoBlock
    /\ ledger[block.source] /= NoBlock
    /\ block.signature = ledger[block.previous].signature
    /\ ledger[block.source].type = "send"
    /\ ledger[block.source].destination = block.signature
    /\ ~IsSendReceived(ledger, block.source)
    /\ CalculateHash(block, lastHash, lastHash')
    /\ distributedLedger' =
        [distributedLedger EXCEPT ![node] =
            [@ EXCEPT ![lastHash'] = block]]

(***************************************************************************)
(* Creation of a rep change block. This action allows Byzantine behaviour, *)
(* with the node specifying an arbitrary block in its possession as the    *)
(* previous block.                                                         *)
(***************************************************************************)
CreateChangeRepBlock(node) ==
    /\ \E prevHash \in Hash :
        /\ \E newRep \in Account :
            LET newChangeRepBlock ==
                [previous |-> prevHash,
                representative |-> newRep,
                type |-> "change",
                signature |-> PrivateKey[node]]
            IN
            /\ distributedLedger[node][prevHash] /= NoBlock
            /\ received' =
                [n \in Node |->
                    received[n] \cup {newChangeRepBlock}]
            /\ UNCHANGED <<distributedLedger, lastHash>>

(***************************************************************************)
(* A node validates a change block before confirming it. Checks include:   *)
(*  - The node's ledger contains the referenced previous block             *)
(*  - The block is signed by the correct account                           *)
(***************************************************************************)
ProcessChangeRepBlock(node, block) ==
    LET ledger == distributedLedger[node] IN
    /\ block.type = "change"
    /\ ledger[block.previous] /= NoBlock
    /\ block.signature = ledger[block.previous].signature
    /\ CalculateHash(block, lastHash, lastHash')
    /\ distributedLedger' =
        [distributedLedger EXCEPT ![node] =
            [@ EXCEPT ![lastHash'] = block]]

(***************************************************************************)
(* Top-level actions.                                                      *)
(***************************************************************************)
CreateBlock(node) ==
    \/ CreateOpenBlock(node)
    \/ CreateSendBlock(node)
    \/ CreateReceiveBlock(node)
    \/ CreateChangeRepBlock(node)

ProcessBlock(node) ==
    /\ \E block \in received[node] :
        /\  \/ ProcessOpenBlock(node, block)
            \/ ProcessSendBlock(node, block)
            \/ ProcessReceiveBlock(node, block)
            \/ ProcessChangeRepBlock(node, block)
        /\ received' = [received EXCEPT ![node] = @ \ {block}]

Init ==
    /\ lastHash = NoHash
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

Next ==
    \/ \E account \in Account : CreateGenesisBlock(account)
    \/ \E node \in Node : CreateBlock(node)
    \/ \E node \in Node : ProcessBlock(node)

=============================================================================