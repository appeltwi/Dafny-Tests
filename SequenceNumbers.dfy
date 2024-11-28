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

predicate LessThan(bi1: byte, bi2:byte)
{
    (bi1 < bi2 && (bi2 - bi1) < 128) 
    || 
    (bi1 > bi2 && (bi1 - bi2) > 128)
}

predicate Simple_less(bi1: int, bi2:int)
{
    bi1 < bi2
}

predicate LessThanOrig(bi1: byte, bi2:byte)
{
    !(((bi1 > 128) && (bi1 > bi2 && bi2 > bi1 - 128)) 
    ||
    ((bi1 <= 128) && (bi1 > bi2 || bi2 > bi1 + 128)))
}

predicate LessThanFixed(bi1: byte, bi2:byte)
{
    !(((bi1 > 128) && (bi1 >= bi2 && bi2 >= bi1 - 128)) 
    ||
    ((bi1 <= 128) && (bi1 >= bi2 || bi2 >= bi1 + 128)))
}

lemma Shift(bi1: byte, bi2:byte, bi3: byte)
ensures LessThan(bi1, bi2) == LessThan((bi1 + bi3) % 256, (bi2 + bi3) % 256)
{

}

lemma Shiftn(i1: int, i2:int, i3: int)
    ensures Simple_less(i1, i2)  == (Simple_less(i1 - i3 ,i2 - i3))
{

}

lemma Compare0(bi1: byte, bi2:byte)
    requires bi1 > 128 && bi2 > bi1 - 128
    ensures Simple_less(bi1, bi2) ==> LessThanFixed(bi1, bi2)
{

}

lemma Compare1(bi1: byte, bi2:byte)
    ensures LessThan(bi1, bi2) ==> LessThanFixed(bi1, bi2)
{

}

lemma Compare2(bi1: byte, bi2:byte)
    requires bi2 - bi1 !=  128 && bi2 - bi1 !=  -128 && bi1 != bi2
    ensures LessThanFixed(bi1, bi2) ==> LessThan(bi1, bi2)
{

}

lemma Compare2a(bi1: byte, bi2:byte)
    ensures LessThanFixed(bi1, bi2) ==> (LessThan(bi1, bi2))
{

}

lemma Compare3(bi1: byte, bi2:byte)
    ensures LessThanFixed(bi1, bi2) <==> (LessThan(bi1, bi2))
{

}

lemma Shift2(bi1: byte, bi2:byte, bi3: byte)
    requires bi2 - bi1 !=  128 && bi1 - bi2 !=  128 
ensures LessThanFixed(bi1, bi2) == LessThanFixed((bi1 + bi3) % 256, (bi2 + bi3) % 256)
{

}

lemma Compare4(i1: nat, i2:nat)
    requires -128 < i1 - i2 < 128
	ensures i1 < i2 ==> LessThan(i1 % 256, i2 % 256)
	ensures i2 < i1 ==> LessThan(i2 % 256, i1 % 256)
{

}

lemma Compare5(i1: nat, i2:nat)
    requires -128 < i1 - i2 < 128
	ensures i1 < i2 ==> LessThanFixed(i1 % 256, i2 % 256)
	ensures i2 < i1 ==> LessThanFixed(i2 % 256, i1 % 256)
{

}

lemma transn(i1: int, i2:int, i3: int)
ensures (i1 < i2) && (i2 < i3) ==> (i1 < i3)
{

}

lemma trans(bi1: byte, bi2:byte, bi3: byte)
requires -64 < bi1 - bi2 < 128 && -64 < bi2 - bi3 < 128
ensures LessThan(bi1, bi2) && LessThan(bi2, bi3) ==> LessThan(bi1, bi3)
{

}

datatype Threeway = equivalent | less | greater | unordered

function ThreeWay(i1: byte, i2:byte) :Threeway
{
    if (i1 == i2) then  equivalent
    else if (LessThan(i1, i2)) then less
    else if (LessThan(i2, i1)) then greater
    else unordered
}

function ThreeWay2(i1: byte, i2:byte) :Threeway
{
    if (i1 == i2) then  equivalent    
    else if (LessThan(i1, i2)) then less
    else if (LessThan(i2, i1)) then greater
    else unordered
}

lemma compareTwoLess(i1: byte, i2:byte)
    ensures ThreeWay(i1, i2) == less <== ThreeWay2(i1, i2) == less
{

}

lemma compareTwoGreater(i1: byte, i2:byte)
    ensures ThreeWay(i1, i2) == greater <== ThreeWay2(i1, i2) == greater
{

}

lemma compareTwoEquiv(i1: byte, i2:byte)
    ensures ThreeWay(i1, i2) == equivalent ==> ThreeWay2(i1, i2) == equivalent
{

}

datatype Option<+T> = Nil | Some(Data: T)

method MinMax(i1: byte, i2:byte) returns (Min: Option<byte>, Max: Option<byte>)
	ensures LessThan(i1, i2) ==> Max == Some((i2 % 256) as byte) && Min == Some((i1 % 256) as byte) 
	ensures LessThan(i2, i1) ==> Max == Some((i1 % 256) as byte) && Min == Some((i2 % 256) as byte)
    ensures i2 == i1 ==> Max == Some((i1 % 256) as byte) && Min == Some((i2 % 256) as byte)
    ensures (!LessThan(i1, i2) && !LessThan(i2, i1) && !(i2 == i1)) ==> Max == Nil && Min == Nil
{
    match ThreeWay(i1, i2)
    {
        case less => Max, Min := Some(i2), Some(i1);
        case greater => Max, Min :=  Some(i1), Some(i2);
        case equivalent => Max, Min := Some(i1), Some(i2);     
        case unordered => Max, Min := Nil, Nil;
    }
}

method MinMax2(i1: byte, i2:byte) returns (Min: byte, Max: byte)
	ensures LessThan(i1, i2) ==> Max == (i2 % 256) as byte && Min == (i1 % 256) as byte 
	ensures LessThan(i2, i1) ==> Max == (i1 % 256) as byte && Min == (i2 % 256) as byte
    ensures (!LessThan(i1, i2) && !LessThan(i2, i1)) ==> Max == (i1 % 256) as byte && Min == (i2 % 256) as byte
{
   match ThreeWay(i1, i2)
   {
        case less => Max, Min := i2, i1;
        case greater => Max, Min := i1, i2;
        case equivalent => Max, Min := i1, i2;        
        case unordered => Max, Min := i1, i2;
    }
}

method SequenceNumberMinMax(i1: nat, i2:nat) returns (Min: byte, Max: byte)
    requires -128 < i1 - i2 < 128
	ensures i1 < i2  ==> Max == (i2 % 256) as byte && Min == (i1 % 256) as byte 
	ensures i2 <= i1 ==> Max == (i1 % 256) as byte && Min == (i2 % 256) as byte 
{
    var bi1 := (i1 % 256) as byte;
    var bi2 := (i2 % 256) as byte;
    var MinOpt2, MaxOpt2 := MinMax(bi1, bi2);    
    assert(MinOpt2 != Nil && MaxOpt2 != Nil);
    Max, Min := MaxOpt2.Data, MinOpt2.Data;

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

    assert(LessThan(128, 0) == LessThan(0, 128));// unordered     
    assert(LessThan(128, 1) == LessThan(0, 129));       
    var ll := LessThan(128, 0) ;
    assert(!ll); // unordered     

    assert(LessThanFixed(128, 0) == LessThanFixed(0, 128));// ordered     
    assert(LessThanFixed(128, 1) == LessThanFixed(0, 129));   
    var wll := LessThanFixed(128, 0);
    assert(!wll);       

    var ll2 := LessThan(255, 0);
    var ll3 := LessThan(0, 255);
    assert(ll2); // ordered     
    assert(!ll3);   

    var Mini, Maxi := MinMax(0, 255);   
    assert(Mini.Data == 255); // ordered     
    assert(Maxi.Data == 0); // ordered    
    Mini, Maxi := MinMax(128, 0); 
    assert(Mini == Nil); // unordered     
    assert(Maxi == Nil); // unordered       

    assert(!LessThan(1, 1));
}
