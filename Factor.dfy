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

method Facotrn(n: int) returns (q: int, e: int)
requires n >= 1
requires isEven(n)
ensures e >= 0
ensures n == q * exp(2, e) + 1
{
    q := n-1;
    e:= 0;
    while(isEven(q))
        decreases q
        invariant q > 0 
        invariant q * exp(2,e) == n -1
    {
        q, e := q / 2, e+ 1;
    }
}



