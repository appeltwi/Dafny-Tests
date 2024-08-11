predicate isEven(a: nat)
{
    a % 2 == 0
}

type EvenInt = x: nat | isEven(x) witness 2
type OddInt = x: nat | !isEven(x) witness 3

predicate divider(a: nat, b:int, k :nat)
{
    b == k * a
}

ghost predicate divides(a: nat, b:int)
{
    exists k: nat :: divider(a, b, k) 
}

ghost predicate prime(p: nat)
{
  (forall k: nat :: 1 < k < p - 1  ==> !divides(k, p)) && p >= 2 
}

type PrimeInt = x: nat | prime(x) witness 3

function exp(x: nat, n: nat): nat
{
    if n == 0 then 
        1
    else 
        x * exp(x, n-1)
}

method Factor(n: PrimeInt) returns (q: nat, e: nat)
requires n >= 3
ensures n == q * exp(2, e) + 1
ensures q >= 1
ensures !isEven(q)
{
    q := n-1;
    e:= 0;
    while(isEven(q))
        decreases q
        invariant q >= 1 
        invariant n == q * exp(2,e) + 1
    {
        q, e := q / 2, e+ 1;
    }
}

lemma EvenNumberIsDivisibleByTwoIndirect(n : nat) 
    requires isEven(n)
    requires n > 0
    ensures divides(2, n)
{   
    if (!divides(2, n))
    {
         assert(!divides(2, n)); 
         var k := n / 2; // wittness
         assert(!divider(2, n, k));
         assert(!isEven(n));
    }
}

lemma EvenNumberIsDivisibleByTwo(n : nat)
    requires isEven(n)
    requires n > 0
    ensures divides(2, n)
{
    var k := n / 2; // wittness
    assert(divider(2, n, k));
    assert(divides(2, n)); 
}

lemma PrimeNumbersAreOdd(p: nat) 
  requires prime(p)
  requires p >=3
  ensures(!isEven(p))
{	
    if (isEven(p))
    {
        assert(p % 2 == 0); 
        EvenNumberIsDivisibleByTwo(p);
        assert(divides(2, p));  
        assert(!prime(p));
    }
}

