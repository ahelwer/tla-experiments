----------------------- MODULE HashFunctionInterface -----------------------
CONSTANTS
    CalcHash(_),        \* A CalcHash(data) step represents calculating the
                        \* hash of a data value.
    GetHash(_),         \* A GetHash(data, hashFunctionInt) call returns the
                        \* previously-calculated hash value of the data.
    Data,               \* The set of hash function input values.
    Hash                \* The set of hash function output values.

ASSUME
    \A data, hfIntOld, hfIntNew :
        /\ CalcHash(data) \in BOOLEAN

ASSUME
    \A data, hf :
        /\ GetHash(data) \in Hash

-----------------------------------------------------------------------------

NoHash == CHOOSE h : h \notin Hash

=============================================================================