method Max(a: int, b:int) returns (c: int)
	ensures a < b  ==> c == b
	ensures b <= a ==> c == a
{
	if (a < b) 
    {
		return b;
	} 
    else 
    {
		return a;
	}
}

type byte = x | 0 <= x < 256


predicate BitVector_Less(bi1: byte, bi2:byte)
{
    (bi1 < bi2 && (bi2 - bi1) < 128) || (bi1 > bi2 && (bi1 - bi2) > 128)
}

function abs(x: int): int
{
	if x < 0 then -x else x
}

datatype Option<+T> = Nil | Some(Data: T)

method MinMax(i1: byte, i2:byte) returns (Min: Option<byte>, Max: Option<byte>)
	ensures BitVector_Less(i1, i2) ==> Max == Some((i2 % 256) as byte) && Min == Some((i1 % 256) as byte) 
	ensures BitVector_Less(i2, i1) ==> Max == Some((i1 % 256) as byte) && Min == Some((i2 % 256) as byte)
    ensures i2 == i1 ==> Max == Some((i1 % 256) as byte) && Min == Some((i2 % 256) as byte)
    ensures (!BitVector_Less(i1, i2) && !BitVector_Less(i2, i1) && !(i2 == i1)) ==> Max == Nil && Min == Nil
{
	if (BitVector_Less(i1, i2)) 
    {
        Max, Min := Some(i2), Some(i1);
	} 
    else if (BitVector_Less(i2, i1) || i2 == i1)
    {
        Max, Min := Some(i1), Some(i2);
	}
    else
    {
        Max, Min:= Nil, Nil;
    }
}

method MinMax2(i1: byte, i2:byte) returns (Min: byte, Max: byte)
    requires BitVector_Less(i1, i2) || BitVector_Less(i2, i1) || i2 == i1
	ensures BitVector_Less(i1, i2) ==> Max == (i2 % 256) as byte && Min == (i1 % 256) as byte 
	ensures (BitVector_Less(i2, i1) || i2 == i1) ==> Max == (i1 % 256) as byte && Min == (i2 % 256) as byte
{
	if (BitVector_Less(i1, i2)) 
    {
        Max, Min := i2, i1;
	} 
    else 
    {
        Max, Min := i1, i2;
	}
}

method SequenceNumberMinMax(i1: nat, i2:nat) returns (Min: byte, Max: byte)
    requires -128 < i1 - i2 < 129
	ensures i1 < i2  ==> Max == (i2 % 256) as byte && Min == (i1 % 256) as byte 
	ensures i2 <= i1 ==> Max == (i1 % 256) as byte && Min == (i2 % 256) as byte 
{
    var bi1 := (i1 % 256) as byte;
    var bi2 := (i2 % 256) as byte;
    var MinOpt, MaxOpt := MinMax(bi1, bi2);
    if (MinOpt.Some? && MaxOpt.Some?)
    {
        Max, Min := MaxOpt.Data, MinOpt.Data;
    }
    else
    {
        Max, Min := bi1, bi2;
    }
}


method TestMax()
{
    var test1 := (-127) % 256;   
    assert(test1 == 129);
    var MinTest, MaxTest := SequenceNumberMinMax(1, 128);
    assert(128 == MaxTest);
    assert(1 == MinTest);    
    var MinTest1, MaxTest1 := SequenceNumberMinMax(128, 129);
    assert(129 == MaxTest1);
    assert(128 == MinTest1);    
    var Mintest2, MaxTest2 := SequenceNumberMinMax(129, 255);
    assert(255 == MaxTest2);    
    assert(129 == Mintest2);    
    var Mintest3, MaxTest3 := SequenceNumberMinMax(255, 256);
    assert(0 == MaxTest3);   
    assert(255 == Mintest3);  
    var Mintest4, MaxTest4 := SequenceNumberMinMax(256, 300);
    assert(44 == MaxTest4);   
    assert(0 == Mintest4);   

    var ll := BitVector_Less(128, 0);
    var ll1 := BitVector_Less(0, 128);
    assert(!ll1); // unordered     
    assert(!ll);   

    var ll2 := BitVector_Less(255, 0);
    var ll3 := BitVector_Less(0, 255);
    assert(ll2); // ordered     
    assert(!ll3);   

    var Mini, Maxi := MinMax(0, 255);   
    assert(Mini.Data == 255); // ordered     
    assert(Maxi.Data == 0); // ordered    
    Mini, Maxi := MinMax(128, 0); 
    assert(Mini == Nil); // unordered     
    assert(Maxi == Nil); // unordered       

    assert(!BitVector_Less(1, 1));
}