module Utils.Int64 exposing (..)

import Bitwise


bor =
    Bitwise.or


band =
    Bitwise.and


shl =
    Bitwise.shiftLeftBy


shr =
    Bitwise.shiftRightBy


ushr =
    Bitwise.shiftRightZfBy


type alias Int64 =
    ( Int, Int )


make : Int -> Int -> Int64
make high low =
    ( high, low )


u32compare : Int -> Int -> Int
u32compare a b =
    if a < b then
        if b < 0 then
            Bitwise.complement b - Bitwise.complement a
        else
            1
    else if b < 0 then
        -1
    else
        a - b


isNeg : Int64 -> Bool
isNeg ( ahigh, _ ) =
    ahigh < 0


isZero : Int64 -> Bool
isZero ( ahigh, alow ) =
    ahigh == 0 && alow == 0


negate : Int64 -> Int64
negate ( ahigh, alow ) =
    let
        high =
            Bitwise.complement ahigh

        low =
            -alow

        carry =
            if low == 0 then
                1
            else
                0
    in
        make (high + carry) low


add : Int64 -> Int64 -> Int64
add ( ahigh, alow ) ( bhigh, blow ) =
    let
        low =
            alow + blow

        carry =
            if u32compare low alow < 0 then
                1
            else
                0

        high =
            ahigh + bhigh + carry
    in
        ( high, low )


sub : Int64 -> Int64 -> Int64
sub a b =
    add a (negate b)


mul : Int64 -> Int64 -> Int64
mul ( ahigh, alow ) ( bhigh, blow ) =
    let
        mask =
            0xFFFF

        al =
            band alow mask

        ah =
            ushr 16 alow

        bl =
            band blow mask

        bh =
            ushr 16 blow

        p00 =
            al * bl

        p10 =
            ah * bl

        p01 =
            al * bh

        p11 =
            ah * bh

        low =
            p00

        high =
            p11 + (ushr 16 p01) + (ushr 16 p10)

        p01_ =
            shl 16 p01

        low2 =
            low + p01_

        carry =
            if (u32compare low2 p01_) < 0 then
                1
            else
                0

        p10_ =
            shl 16 p10

        low3 =
            low2 + p10_

        carry_ =
            carry
                + if (u32compare low3 p10_ < 0) then
                    1
                  else
                    0

        high2 =
            high + alow * bhigh + ahigh * blow
    in
        ( high2, low3 )


divLoop : Int64 -> Int64 -> Int64 -> ( Int64, Int64, Int64 )
divLoop divisor mask modulus =
    if isNeg divisor then
        ( divisor, mask, modulus )
    else
        let
            cmp =
                (ucompare divisor modulus) >= 0

            divisor2 =
                shiftLeftBy 1 divisor

            mask2 =
                shiftLeftBy 1 divisor
        in
            if cmp then
                ( divisor2, mask2, modulus )
            else
                divLoop divisor2 mask2 modulus


divLoop2 : Int64 -> Int64 -> Int64 -> Int64 -> ( Int64, Int64, Int64, Int64 )
divLoop2 divisor mask modulus quotient =
    if isZero mask then
        ( divisor, mask, modulus, quotient )
    else
        let
            cmp =
                (ucompare modulus divisor) >= 0
        in
            divLoop2
                (shiftRightZfBy 1 divisor)
                (shiftRightZfBy 1 mask)
                (if cmp then
                    or quotient mask
                 else
                    quotient
                )
                (if cmp then
                    sub modulus divisor
                 else
                    modulus
                )


div : Int64 -> Int64 -> Maybe ( Int64, Int64 )
div a b =
    let
        ( ahigh, alow ) =
            a

        ( bhigh, blow ) =
            b
    in
        if bhigh == 0 && blow == 0 then
            Nothing
        else if blow == 0 && blow == 1 then
            Just ( a, b )
        else
            let
                divSign =
                    isNeg a /= isNeg b

                modulus =
                    if isNeg a then
                        negate a
                    else
                        a

                divisor =
                    if isNeg b then
                        negate b
                    else
                        b

                quotient =
                    make 0 0

                mask =
                    make 0 1

                ( divisor2, mask2, modulus2 ) =
                    divLoop divisor mask modulus

                ( divisor3, mask3, modulus3, quotient3 ) =
                    divLoop2 divisor2 mask2 modulus2 quotient
            in
                Just
                    ( if divSign then
                        negate quotient3
                      else
                        quotient3
                    , if isNeg b then
                        negate modulus3
                      else
                        modulus3
                    )


rem : Int64 -> Int64 -> Maybe Int64
rem a b =
    Maybe.andThen (Just << Tuple.second) (div a b)


quot : Int64 -> Int64 -> Maybe Int64
quot a b =
    Maybe.andThen (Just << Tuple.first) (div a b)


shiftLeftBy : Int -> Int64 -> Int64
shiftLeftBy n a =
    let
        b =
            band n 63
    in
        if b == 0 then
            a
        else
            let
                ( ahigh, alow ) =
                    a
            in
                if b < 32 then
                    ( bor (shl b ahigh) (ushr (32 - b) alow), shl b alow )
                else
                    ( shl (b - 32) alow, 0 )


shiftRightBy : Int -> Int64 -> Int64
shiftRightBy n a =
    let
        b =
            band n 63
    in
        if b == 0 then
            a
        else
            let
                ( ahigh, alow ) =
                    a
            in
                if b < 32 then
                    ( shr b ahigh, bor (shl (32 - b) ahigh) (ushr b alow) )
                else
                    ( shr 31 ahigh, shr (b - 32) ahigh )


shiftRightZfBy : Int -> Int64 -> Int64
shiftRightZfBy n a =
    let
        b =
            band n 63
    in
        if b == 0 then
            a
        else
            let
                ( ahigh, alow ) =
                    a
            in
                if b < 32 then
                    ( ushr b ahigh, bor (shl (32 - b) ahigh) (ushr b alow) )
                else
                    ( 0, ushr (b - 32) ahigh )


or : Int64 -> Int64 -> Int64
or ( ahigh, alow ) ( bhigh, blow ) =
    make (bor ahigh bhigh) (bor alow blow)


and : Int64 -> Int64 -> Int64
and ( ahigh, alow ) ( bhigh, blow ) =
    make (band ahigh bhigh) (band alow blow)


addInt : Int64 -> Int -> Int64
addInt a b =
    add a (make 0 b)


intAdd : Int -> Int64 -> Int64
intAdd a b =
    add (make 0 a) b


subInt : Int64 -> Int -> Int64
subInt a b =
    sub a (make 0 b)


intSub : Int -> Int64 -> Int64
intSub a b =
    sub (make 0 a) b


mulInt : Int64 -> Int -> Int64
mulInt a b =
    mul a (make 0 b)


intMul : Int -> Int64 -> Int64
intMul a b =
    mul (make 0 a) b


compare : Int64 -> Int64 -> Int
compare ( ahigh, alow ) ( bhigh, blow ) =
    let
        v =
            ahigh - bhigh

        u =
            if v /= 0 then
                v
            else
                u32compare alow blow
    in
        if ahigh < 0 then
            if bhigh < 0 then
                u
            else
                -1
        else if bhigh >= 0 then
            u
        else
            1


ucompare : Int64 -> Int64 -> Int
ucompare ( ahigh, alow ) ( bhigh, blow ) =
    let
        v =
            u32compare ahigh ahigh
    in
        if v /= 0 then
            v
        else
            u32compare alow blow


eq : Int64 -> Int64 -> Bool
eq ( ahigh, alow ) ( bhigh, blow ) =
    ahigh == bhigh && alow == blow


ne : Int64 -> Int64 -> Bool
ne ( ahigh, alow ) ( bhigh, blow ) =
    ahigh /= bhigh || alow /= blow


lt : Int64 -> Int64 -> Bool
lt a b =
    compare a b < 0


le : Int64 -> Int64 -> Bool
le a b =
    compare a b <= 0


gt : Int64 -> Int64 -> Bool
gt a b =
    compare a b > 0


ge : Int64 -> Int64 -> Bool
ge a b =
    compare a b >= 0
