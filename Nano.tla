-------------------------------- MODULE Nano --------------------------------
EXTENDS
    FiniteSets,
    Integers,
    Sequences

CONSTANTS
    Account,
    Node,
    Hash,
    GenesisBalance

VARIABLES
    DistributedLedger,
    Received,
    HashFunction

-----------------------------------------------------------------------------

(***************************************************************************)
(* Defines blockchains, ledgers, and the set of valid transactions.        *)
(***************************************************************************)

NoHash == CHOOSE h : h \notin Hash

AccountBalance == 0 .. GenesisBalance

OpenAccountTx == [
    type : {"open"},
    account : Account,
    source : Hash,
    representative : Account,
    signature : Account]

SendTx == [
    previous : Hash,
    balance : AccountBalance,
    destination : Account,
    type : {"send"},
    signature : Account]

ReceiveTx == [
    previous : Hash,
    source : Hash,
    type : {"receive"},
    signature : Account]

ChangeRepresentativeTx == [
    previous: Hash,
    representative : Account,
    type : {"change"},
    signature : Account]

GenesisTx == [
    type : {"genesis"},
    account : Account,
    balance : {GenesisBalance},
    signature : Account]

Transaction ==
    OpenAccountTx
    \cup SendTx
    \cup ReceiveTx
    \cup ChangeRepresentativeTx
    \cup GenesisTx

Blockchain == Seq(Transaction)

NoTransaction == CHOOSE tx : tx \notin Transaction

Ledger == [Hash -> Transaction \cup {NoTransaction}]

(***************************************************************************)
(* Functions to calculate account balances and transaction values.         *)
(***************************************************************************)

Last(s) ==  \* Returns the last element in a sequence.
    s[Len(s)]

RECURSIVE BalanceAt(_, _)
RECURSIVE ValueOfSendTransaction(_, _)

BalanceAt(ledger, hash) ==
    LET tx == ledger[hash] IN
    CASE tx.type = "open" -> ValueOfSendTransaction(ledger, tx.source)
    [] tx.type = "send" -> tx.balance
    [] tx.type = "receive" ->
        BalanceAt(ledger, tx.previous)
        + ValueOfSendTransaction(ledger, tx.source)
    [] tx.type = "genesis" -> tx.balance

ValueOfSendTransaction(ledger, hash) ==
    LET tx == ledger[hash] IN
    BalanceAt(ledger, tx.previous) - tx.balance
 
(***************************************************************************)
(* The type & safety invariants.                                           *)
(***************************************************************************)
TypeInvariant ==
    /\ DistributedLedger \in [Node -> Ledger]
    /\ Received \in [Node -> SUBSET Transaction]
    /\ HashFunction \in [Transaction -> Hash \cup {NoHash}]

SafetyInvariant ==
    /\ \A tx \in Transaction :
        /\ HashFunction[tx] /= NoHash <=>
            /\ \E n \in Node :
                /\ DistributedLedger[n][HashFunction[tx]] = tx
            /\ \A n \in Node :
                /\ DistributedLedger[n][HashFunction[tx]] \in {NoTransaction, tx}

(***************************************************************************)
(* Creation & processing of send transactions.                             *)
(***************************************************************************)
CreateSendTx(node, srcAccount, dstAccount, newBalance) ==
    /\ \E newHash, prevHash \in Hash :
        LET newSendTx ==
            [previous |-> prevHash,
            balance |-> newBalance,
            destination |-> dstAccount,
            type |-> "send",
            signature |-> srcAccount]
        IN
        /\  \/ HashFunction[newSendTx] = newHash
            \/ \A tx \in Transaction : HashFunction[tx] /= newHash
        /\ DistributedLedger[node][prevHash] /= NoTransaction
        /\ Received' = [n \in Node |-> Received[n] \cup {newSendTx}]
        /\ HashFunction' = [HashFunction EXCEPT ![newSendTx] = newHash]
        /\ UNCHANGED <<DistributedLedger>>

ProcessSendTransaction(n, tx) ==
    LET txHash == HashFunction[tx] IN
    LET ledger == DistributedLedger[n] IN
    /\ tx.type = "send"
    /\ ledger[tx.previous] /= NoTransaction
    /\ tx.signature = ledger[tx.previous].signature
    /\ tx.destination /= tx.signature
    /\ tx.balance < BalanceAt(ledger, tx.previous)
    /\ DistributedLedger' =
        [DistributedLedger EXCEPT ![n] =
            [@ EXCEPT ![txHash] = tx]]

(***************************************************************************)
(* Creation & processing of receive transactions.                          *)
(***************************************************************************)
CreateReceiveTx(node, account) ==
    \E newHash, prevHash, srcHash \in Hash :
        LET newRcvTx ==
            [previous |-> prevHash,
            source |-> srcHash,
            type |-> "receive",
            signature |-> account]
        IN
        /\  \/ HashFunction[newRcvTx] = newHash
            \/ \A tx \in Transaction : HashFunction[tx] /= newHash
        /\ DistributedLedger[node][prevHash] /= NoTransaction
        /\ DistributedLedger[node][srcHash] /= NoTransaction
        /\ Received' = [n \in Node |-> Received[n] \cup {newRcvTx}]
        /\ HashFunction' = [HashFunction EXCEPT ![newRcvTx] = newHash]
        /\ UNCHANGED <<DistributedLedger>>

ProcessReceiveTransaction(n, tx) ==
    LET txHash == HashFunction[tx] IN
    LET ledger == DistributedLedger[n] IN
    /\ tx.type = "receive"
    /\ ledger[tx.previous] /= NoTransaction
    /\ ledger[tx.source] /= NoTransaction
    /\ tx.signature = ledger[tx.previous].signature
    /\ ledger[tx.source].type = "send"
    /\ ledger[tx.source].destination = tx.signature
    /\ DistributedLedger' =
        [DistributedLedger EXCEPT ![n] =
            [@ EXCEPT ![txHash] = tx]]

(***************************************************************************)
(* Creation & processing of account open transactions.                     *)
(***************************************************************************)
CreateOpenAccountTransaction(n, tx) == TRUE

ProcessOpenAccountTransaction(n, tx) == TRUE

(***************************************************************************)
(* Creation & processing of representative change transactions.            *)
(***************************************************************************)
CreateChangeRepresentativeTransaction(n, tx) == TRUE

ProcessChangeRepresentativeTransaction(n, tx) == TRUE


(***************************************************************************)
(* Top-level actions.                                                      *)
(***************************************************************************)
ProcessTransaction(n) ==
    /\ \E tx \in Received[n] :
        /\ CASE tx.type = "open" -> ProcessOpenAccountTransaction(n, tx)
            [] tx.type = "send" -> ProcessSendTransaction(n, tx)
            [] tx.type = "receive" -> ProcessReceiveTransaction(n, tx)
            [] tx.type = "change" -> ProcessChangeRepresentativeTransaction(n, tx)
        /\ Received' = [Received EXCEPT ![n] = @ \ {tx}]
    /\ UNCHANGED <<HashFunction>>

Next ==
    \/ \E node \in Node :
        \/ \E srcAccount, dstAccount \in Account :
            /\ \E newBalance \in AccountBalance :
                /\ CreateSendTx(node, srcAccount, dstAccount, newBalance)
        \/ \E account \in Account :
            /\ CreateReceiveTx(node, account)
    \/ \E n \in Node :
        /\ ProcessTransaction(n)

(***************************************************************************)
(* System initialization. Only the genesis account is open.                *)
(***************************************************************************)
Init ==
    /\ \E genesisHash \in Hash :
        /\ \E genesisAccount \in Account :
            LET genesisBlock ==
                [type |-> "genesis",
                account |-> genesisAccount,
                balance |-> GenesisBalance,
                signature |-> genesisAccount]
            IN
            /\ DistributedLedger =
                [n \in Node |->
                    [h \in Hash |->
                        IF h = genesisHash
                        THEN genesisBlock
                        ELSE NoTransaction]]
            /\ HashFunction =
                [tx \in Transaction |->
                    IF tx = genesisBlock
                    THEN genesisHash
                    ELSE NoHash]
    /\ Received = [n \in Node |-> {}]

=============================================================================