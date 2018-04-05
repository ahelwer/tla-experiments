-------------------------------- MODULE Nano --------------------------------
EXTENDS
    Naturals

CONSTANTS
    Hash,
    CalculateHash(_,_,_),
    Account,
    Node,
    GenesisBalance,
    PrivateKey,
    ValidateCreatedBlocks

VARIABLES
    lastHash,
    distributedLedger,
    received

ASSUME \A block, oldLastHash, newLastHash :
    CalculateHash(block, oldLastHash, newLastHash) \in BOOLEAN

ASSUME PrivateKey \in [Node -> Account]

ASSUME ValidateCreatedBlocks \in BOOLEAN

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
(* Creation, validation, and confirmation of open blocks. Checks include:  *)
(*  - The block is signed by the private key of the account being opened   *)
(*  - The node's ledger contains the referenced source block               *)
(*  - The source block is a send block to the account being opened         *)
(***************************************************************************)

ValidateOpenBlock(ledger, block) ==
    LET sourceBlock == ledger[block.source] IN
    /\ block.type = "open"
    /\ block.signature = block.account
    /\ sourceBlock /= NoBlock
    /\ sourceBlock.type = "send"
    /\ sourceBlock.destination = block.account

CreateOpenBlock(node) ==
    LET ledger == distributedLedger[node] IN
    /\ \E newAccount, repAccount \in Account :
        /\ \E srcHash \in Hash :
            LET newOpenBlock ==
                [account |-> newAccount,
                source |-> srcHash,
                representative |-> repAccount,
                type |-> "open",
                signature |-> PrivateKey[node]]
            IN
            /\ ledger[srcHash] /= NoBlock
            /\ ValidateCreatedBlocks =>
                /\ ValidateOpenBlock(ledger, newOpenBlock)
            /\ CalculateHash(newOpenBlock, lastHash, lastHash')
            /\ received' =
                [n \in Node |->
                    received[n] \cup {newOpenBlock}]
            /\ UNCHANGED distributedLedger

ProcessOpenBlock(node, block) ==
    LET ledger == distributedLedger[node] IN
    /\ ValidateOpenBlock(ledger, block)
    /\ ~IsAccountOpen(ledger, block.account)
    /\ CalculateHash(block, lastHash, lastHash')
    /\ distributedLedger' =
        [distributedLedger EXCEPT ![node] =
            [@ EXCEPT ![lastHash'] = block]]

(***************************************************************************)
(* Creation, validation, and confirmation of send blocks. Checks include:  *)
(*  - The node's ledger contains the referenced previous block             *)
(*  - The block is signed by the account sourcing the funds                *)
(*  - The value sent is non-negative                                       *)
(***************************************************************************)

ValidateSendBlock(ledger, block) ==
    /\ block.type = "send"
    /\ ledger[block.previous] /= NoBlock
    /\ ledger[block.previous].signature = block.signature

CreateSendBlock(node) ==
    LET ledger == distributedLedger[node] IN
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
                /\ ledger[prevHash] /= NoBlock
                /\ ValidateCreatedBlocks =>
                    /\ ValidateSendBlock(ledger, newSendBlock)
                /\ CalculateHash(newSendBlock, lastHash, lastHash')
                /\ received' =
                    [n \in Node |->
                        received[n] \cup {newSendBlock}]
                /\ UNCHANGED distributedLedger

ProcessSendBlock(node, block) ==
    LET ledger == distributedLedger[node] IN
    /\ ValidateSendBlock(ledger, block)
    /\ block.balance <= BalanceAt(ledger, block.previous)
    /\ CalculateHash(block, lastHash, lastHash')
    /\ distributedLedger' =
        [distributedLedger EXCEPT ![node] =
            [@ EXCEPT ![lastHash'] = block]]

(***************************************************************************)
(* Creation, validation, & confirmation of receive blocks. Checks include: *)
(*  - The node's ledger contains the referenced previous & source blocks   *)
(*  - The block is signed by the account sourcing the funds                *)
(*  - The source block is a send block to the receive block's account      *)
(*  - The source block does not already have a corresponding receive/open  *)
(***************************************************************************)

ValidateReceiveBlock(ledger, block) ==
    /\ block.type = "receive"
    /\ ledger[block.previous] /= NoBlock
    /\ ledger[block.previous].signature = block.signature
    /\ ledger[block.source] /= NoBlock
    /\ ledger[block.source].type = "send"
    /\ ledger[block.source].destination = block.signature

CreateReceiveBlock(node) ==
    LET ledger == distributedLedger[node] IN
    \E prevHash, srcHash \in Hash :
        LET newRcvBlock ==
            [previous |-> prevHash,
            source |-> srcHash,
            type |-> "receive",
            signature |-> PrivateKey[node]]
        IN
        /\ ledger[prevHash] /= NoBlock
        /\ ledger[srcHash] /= NoBlock
        /\ ValidateCreatedBlocks =>
            /\ ValidateReceiveBlock(ledger, newRcvBlock)
        /\ CalculateHash(newRcvBlock, lastHash, lastHash')
        /\ received' = [n \in Node |-> received[n] \cup {newRcvBlock}]
        /\ UNCHANGED distributedLedger

ProcessReceiveBlock(node, block) ==
    LET ledger == distributedLedger[node] IN
    /\ ValidateReceiveBlock(ledger, block)
    /\ ~IsSendReceived(ledger, block.source)
    /\ CalculateHash(block, lastHash, lastHash')
    /\ distributedLedger' =
        [distributedLedger EXCEPT ![node] =
            [@ EXCEPT ![lastHash'] = block]]

(***************************************************************************)
(* Creation, validation, & confirmation of change blocks. Checks include:  *)
(*  - The node's ledger contains the referenced previous block             *)
(*  - The block is signed by the correct account                           *)
(***************************************************************************)

ValidateChangeBlock(ledger, block) ==
    /\ block.type = "change"
    /\ ledger[block.previous] /= NoBlock
    /\ block.signature = ledger[block.previous].signature

CreateChangeRepBlock(node) ==
    LET ledger == distributedLedger[node] IN
    /\ \E prevHash \in Hash :
        /\ \E newRep \in Account :
            LET newChangeRepBlock ==
                [previous |-> prevHash,
                representative |-> newRep,
                type |-> "change",
                signature |-> PrivateKey[node]]
            IN
            /\ ledger[prevHash] /= NoBlock
            /\ ValidateCreatedBlocks =>
                /\ ValidateChangeBlock(ledger, newChangeRepBlock)
            /\ CalculateHash(newChangeRepBlock, lastHash, lastHash')
            /\ received' =
                [n \in Node |->
                    received[n] \cup {newChangeRepBlock}]
            /\ UNCHANGED distributedLedger

ProcessChangeRepBlock(node, block) ==
    LET ledger == distributedLedger[node] IN
    /\ ValidateChangeBlock(ledger, block)
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