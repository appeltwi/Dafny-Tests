function isEven(a: nat): bool
{
    a % 2 == 0
}

type EvenInt = x: nat | isEven(x) witness 2
type OddInt = x: nat | !isEven(x) witness 3

function exp(x: nat, n: nat): int
{
    if n == 0 then 
        1
    else 
        x * exp(x, n-1)
}

method Factor(n: OddInt) returns (q: nat, e: nat)
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



