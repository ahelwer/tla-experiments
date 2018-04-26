-------------------------------- MODULE Hex --------------------------------

EXTENDS
    Naturals,
    Sequences,
    TLC

VARIABLES
    hexValue,
    natValue

----------------------------------------------------------------------------

RECURSIVE HighestMultipleLEQ(_, _, _)
HighestMultipleLEQ(a, b, current) ==
    LET next == current + 1 IN
    IF next * b > a
    THEN current
    ELSE HighestMultipleLEQ(a, b, next)

a / b == HighestMultipleLEQ(a, b, 0)

HexDigit == 0 .. 15

Hex == Seq(HexDigit)

HexChar ==
    <<"0","1","2","3","4","5","6","7","8","9","A","B","C","D","E","F">>

RECURSIVE HexToString(_)
HexToString(hex) ==
    IF hex = <<>>
    THEN ""
    ELSE HexChar[Head(hex) + 1] \o HexToString(Tail(hex))

RECURSIVE NatToHex(_)
NatToHex(val) ==
    LET
        prefix == val / 16
        remainder == val % 16
    IN
    IF prefix = 0
    THEN <<remainder>>
    ELSE Append(NatToHex(prefix), remainder)

TypeInvariant ==
    /\ hexValue \in Hex
    /\ natValue \in Nat

SafetyInvariant ==
    /\ hexValue = NatToHex(natValue)

Init ==
    /\ hexValue = <<0>>
    /\ natValue = 0

RECURSIVE IncrementedHexValue(_)
IncrementedHexValue(hex) ==
    LET
        prefix == SubSeq(hex, 1, Len(hex) - 1)
        last == hex[Len(hex)]
    IN
    IF hex = <<>>
    THEN <<1>>
    ELSE
        IF last < 15
        THEN Append(prefix, last + 1)
        ELSE Append(IncrementedHexValue(prefix), 0)

Increment ==
    /\ Print(HexToString(hexValue), TRUE)
    /\ Print(HexToString(NatToHex(natValue)), TRUE)
    /\ hexValue' = IncrementedHexValue(hexValue)
    /\ natValue' = natValue + 1

Next ==
    \/ Increment

=============================================================================