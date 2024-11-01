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


predicate bvless(bi1: nat, bi2:nat)
{
    (bi1 < bi2 && (bi2 - bi1) < 128) || (bi1 > bi2 && (bi1 - bi2) > 128)
}

method SequenceNumberMin(i1: nat, i2:nat) returns (c: byte)
    requires -129 < i1 - i2 < 128
	ensures i1 < i2  ==> c == (i1 % 256) as byte
	ensures i2 <= i1 ==> c == (i2 % 256) as byte
{
    var bi1 := (i2 % 256) as byte;
    var bi2 := (i1 % 256) as byte;
	if (bvless(bi1, bi2)) 
    {
        c := bi1;
	} 
    else 
    {
        c := bi2;
	}
}


method SequenceNumberMax(i1: nat, i2:nat) returns (c: byte)
    requires -129 < i1 - i2 < 128
	ensures i1 < i2  ==> c == (i2 % 256) as byte
	ensures i2 <= i1 ==> c == (i1 % 256) as byte
{
    var bi1 := (i2 % 256) as byte;
    var bi2 := (i1 % 256) as byte;
	if (bvless(bi1, bi2)) 
    {
        c := bi2;
	} 
    else 
    {
        c := bi1;
	}
}

method SequenceNumberMinMax returns (Min: byte, MAx: byte)
{

}

method TestMax()
{
    var MaxTest := SequenceNumberMax(0, 128);
    assert(128 == MaxTest);
    var MaxTest1 := SequenceNumberMax(128, 129);
    assert(129 == MaxTest1);
    var MaxTest2 := SequenceNumberMax(129, 255);
    assert(255 == MaxTest2);    
    var MaxTest3 := SequenceNumberMax(255, 257);
    assert(1 == MaxTest3);       
}