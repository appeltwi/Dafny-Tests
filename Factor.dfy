function isEven(a: int): bool
    requires a >= 0
{
    a % 2 == 0
}

function exp(x: int, n: int): int
    requires n >= 0
{
    if n == 0 then 
        1
    else 
        x * exp(x, n-1)
}

method Factor(n: int) returns (q: int, e: int)
requires n >= 3
requires !isEven(n)
ensures e >= 0
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



