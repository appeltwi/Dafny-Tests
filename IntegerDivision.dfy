opaque function slow_remainder(x: int, n: nat): (int)
    requires n > 0
    decreases x
{
    if x < n then 
        x
    else 
        slow_remainder(x - n, n)
}

lemma congruencems(x: int, n: int)
 requires n > 0
 requires x >= n
 ensures slow_remainder(x, n) == slow_remainder(x - n, n)
 {
    calc
    {
        slow_remainder(x - n, n);       
        { reveal slow_remainder(); }   
        slow_remainder(x, n);  
    }
 }

 lemma multhelp1(a: int, b: int, c: int)
    requires c > 0
    ensures a < b ==> c * a < c *b
 {

 }

  lemma multhelp2(a: int, b: int, c: int)
    requires c > 0
    ensures a > b ==> c * a > c *b
 {

 }

 lemma congruencem(a: int, b: int)
    requires b > 0
     ensures a % b == (a - b) % b
 {
    var y := a - b;
    assert FactoredDiff: (a % b - y % b  == b * (1- a / b + y / b));
    calc <==>
    {
        -b < a % b - y % b < b;
        {reveal FactoredDiff;}
        -b < b * (1- a / b + y / b) < b;  
        {multhelp1((1- a / b + y / b), b, b); multhelp2((1- a / b + y / b), -b, b);}              
        -1 < (1- a / b + y / b) < 1;
        ==> a % b - y % b == 0;
    }   
 }



lemma remainder_test(x: nat, n: nat)
    requires P: n > 0
    ensures  x % n == slow_remainder(x,n)
{

    if (x < n)
    {
        assert(x % n == slow_remainder(x,n))  by { reveal slow_remainder(); }
    }
    else // x >= n
    {
        reveal P;
        var k := x / n;
        calc
        {
            x % n;        
           {  congruencem(x, n); reveal P; }                     
            (x - n) % n;  
           { remainder_test(x - n, n); }    
            slow_remainder(x - n, n);       
           { congruencems(x, n); }   
           slow_remainder(x, n);                                                                           
        } 
    }
}

opaque function pow(x: int, n: int): int
    requires n >= 0
{
    if n == 0 then 
        1  
    else 
        x * pow(x, n-1)
}

method largest_doubling(a: int, b: int) returns (r: int, k: int)
    requires a >= b 
    requires b >0
    ensures k >= 0
    ensures r == pow(2, k) * b
    ensures r <= a < 2 * r 
{
    //r := b * 2;
    //k := 1;
    r:= b;
    k := 0;
    assert( pow(2, k) * b == r)  by { reveal pow(); }
    assert(a >= r);
    while (2 * r <= a)
        invariant r == pow(2, k) * b
        invariant a >= r
    {
        reveal pow();
        r, k := 2 * r, k + 1;      
    }
}

lemma congruencems2(x: int, n: int, k: int)
 requires k > 0
 requires n > 0
 requires x >= k * n + n
 ensures slow_remainder(x, n) == slow_remainder(x - k * n, n)
 {
    if (k == 1)
    {
        congruencems(x, n);
    }
    else
    {
        calc
        {
            slow_remainder(x - k * n, n); 
            slow_remainder(x -  (k - 1) * n - n, n);             
            { congruencems(x - (k - 1) * n, n); }                           
            slow_remainder(x - (k - 1) * n, n); 
           { congruencems2(x, n, k -1); }   
           slow_remainder(x, n);  
        }
    }
 }

// method fast_remainder(a: int, b: int) returns (r: int)
//     requires a >= b 
//     requires b > 0
//     ensures r == slow_remainder(a, b)
// {
//     var c, k := largest_doubling(a, b);
//     assert(c == pow(2, k) * b);  
//     r := a - c; // a = a - pow(2, k) * b
//     reveal slow_remainder();
//     assert(slow_remainder(a, b) == slow_remainder(r, b));
//     while(k > 1)
//         decreases k
//     {
//         c := c / 2;
//         k := k - 1;         
//         if (c <= a)
//         {
//             r := r - c;
//         }
//     }
// }