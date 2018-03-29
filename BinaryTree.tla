----------------------------- MODULE BinaryTree -----------------------------
EXTENDS
    Naturals

CONSTANT
    Address,
    Value

VARIABLES
    Root,
    Memory,
    Added

ASSUME Address \subseteq Nat
ASSUME Value \subseteq Nat

-----------------------------------------------------------------------------

Null == CHOOSE a : a \notin Address

Pointer == Address \cup {Null}

Node ==
    [parent : Pointer,
    value : Value,
    leftChild : Pointer,
    rightChild : Pointer]

NoNode == CHOOSE n : n \notin Node

TypeInvariant ==
    /\ Root \in Pointer
    /\ Memory \in [Address -> Node \cup {NoNode}]
    /\ Added \subseteq Value

RECURSIVE Get(_,_)
Get(currentPointer, v) ==
    IF currentPointer = Null
    THEN Null
    ELSE
        LET current == Memory[currentPointer] IN
        IF current.value = v
        THEN current
        ELSE
            IF current.value < v
            THEN Get(current.rightChild, v)
            ELSE Get(current.leftChild, v)
        
Contains(currentPointer, v) ==
    Get(currentPointer, v) /= Null

SafetyInvariant ==
    /\ Root = Null <=> Added = {}
    /\ \A v \in Value :
        /\ v \in Added <=> Contains(Root, v)
    /\ \A nodeAddress \in Address :
        LET node == Memory[nodeAddress] IN
        /\ node /= NoNode =>
            /\ node.leftChild /= Null =>
                /\ Memory[node.leftChild] /= NoNode
                /\ Memory[node.leftChild].value < node.value
            /\ node.rightChild /= Null =>
                /\ Memory[node.rightChild] /= NoNode
                /\ Memory[node.rightChild].value > node.value
            /\  IF node.parent = Null
                THEN Root = nodeAddress
                ELSE
                    LET parentNode == Memory[node.parent] IN
                    /\ parentNode /= NoNode
                    /\  \/ parentNode.leftChild = nodeAddress
                        \/ parentNode.rightChild = nodeAddress

Init ==
    /\ Root = Null
    /\ Memory = [a \in Address |-> NoNode]
    /\ Added = {}

RECURSIVE ParentOf(_,_)
ParentOf(currentPointer, v) ==
    LET current == Memory[currentPointer] IN
    IF current.value = v
    THEN current.parent
    ELSE
        IF current.value < v
        THEN
            IF current.rightChild /= Null
            THEN ParentOf(current.rightChild, v)
            ELSE currentPointer
        ELSE
            IF current.leftChild /= Null
            THEN ParentOf(current.leftChild, v)
            ELSE currentPointer

InsertLeafNode(nodeParent, v, insertLeft) ==
    /\ \E newNode \in Address :
        /\ Memory[newNode] = NoNode
        /\ Memory' =
            [Memory EXCEPT
                ![newNode] =
                    [parent |-> nodeParent,
                    value |-> v,
                    leftChild |-> Null,
                    rightChild |-> Null],
                ![nodeParent] =
                    IF insertLeft
                    THEN [@ EXCEPT !.leftChild = newNode]
                    ELSE [@ EXCEPT !.rightChild = newNode]]

InsertNode(nodeParentPointer, v) ==
    LET nodeParent == Memory[nodeParentPointer] IN
    IF nodeParent.value < v
    THEN InsertLeafNode(nodeParentPointer, v, FALSE)
    ELSE InsertLeafNode(nodeParentPointer, v, TRUE)

AddRoot(v) ==
    /\ \E newNode \in Address :
        /\ Memory[newNode] = NoNode
        /\ Root' = newNode
        /\ Memory' =
            [Memory EXCEPT ![newNode] =
                [parent |-> Null,
                value |-> v,
                leftChild |-> Null,
                rightChild |-> Null]]

Add(v) ==
    /\ Added' = Added \cup {v}
    /\  IF Contains(Root, v)
        THEN UNCHANGED <<Root, Memory>>
        ELSE
            IF Root = Null
            THEN AddRoot(v)
            ELSE
                /\ InsertNode(ParentOf(Root, v), v)
                /\ UNCHANGED <<Root>>

RemoveLeafNode(nodePointer) ==
    LET node == Memory[nodePointer] IN
    /\ node.leftChild = Null
    /\ node.rightChild = Null
    /\  IF Root = nodePointer
        THEN Root' = Null
        ELSE UNCHANGED <<Root>>
    /\ Memory' =
        [Memory EXCEPT
            ![nodePointer] = NoNode,
            ![node.parent] =
                IF @.leftChild = nodePointer
                THEN [@ EXCEPT !.leftChild = Null]
                ELSE [@ EXCEPT !.rightChild = Null]]

RemoveNodeWithSingleChild(nodePointer) ==
    LET node == Memory[nodePointer] IN
    /\  \/ node.leftChild /= Null
        \/ node.rightChild /= Null
    /\ node.leftChild /= node.rightChild

RemoveNodeWithTwoChildren(nodePointer) == TRUE

Remove(v) ==
    LET nodePointer == Get(Root, v) IN
    /\ Added' = Added \ {v}
    /\  IF nodePointer = Null
        THEN UNCHANGED <<Root, Memory>>
        ELSE
            \/ RemoveLeafNode(nodePointer)
            \/ RemoveNodeWithSingleChild(nodePointer)
            \/ RemoveNodeWithTwoChildren(nodePointer)

Next ==
    \/ \E v \in Value :
        \/ Add(v)
        \/ Remove(v)

=============================================================================