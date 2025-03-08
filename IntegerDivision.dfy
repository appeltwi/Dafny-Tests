opaque function slow_remainder(a: int, b: nat): (int)
    requires b > 0
    decreases a
{
    if a < b then 
        a
    else 
        slow_remainder(a - b, b)
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



lemma remainder_check(x: nat, n: nat)
    requires P: n > 0
    ensures  x % n == slow_remainder(x,n)
{

    if (x < n)
    {
        assert(x % n == slow_remainder(x,n))  by { reveal slow_remainder(); }
    }
    else
    {
        reveal P;
        var k := x / n;
        calc
        {
            x % n;        
           {  congruencem(x, n); reveal P; }                     
            (x - n) % n;  
           { remainder_check(x - n, n); }    
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

lemma congruencems2(a: int, b: int, k: int)
 requires k > 0
 requires b > 0
 requires a >= k * b 
 ensures slow_remainder(a, b) == slow_remainder(a - k * b, b)
 {
    if (k == 1)
    {
        congruencems(a, b);
    }
    else
    {
        calc
        {
            slow_remainder(a - k * b, b); 
            slow_remainder(a -  (k - 1) * b - b, b);             
            { congruencems(a - (k - 1) * b, b); }                           
            slow_remainder(a - (k - 1) * b, b); 
           { congruencems2(a, b, k -1); }   
           slow_remainder(a, b);  
        }
    }
 }

method fast_remainder(a: int, d: int) returns (r: int)
    requires a >= 0
    requires d > 0
    ensures r == slow_remainder(a, d)
{
    if (a < d)
    {
        r:= a;
        assert(r == slow_remainder(a, d)) by {reveal slow_remainder();}        
    }
    else 
    {
        r := a;
        var k := 0;  
        while(r >= d)
        invariant a - r == k * d
        invariant a >= k *d
        invariant r >= 0
        decreases r   
        invariant slow_remainder(r, d) == slow_remainder(a -  k * d , d)
        {

            assert(a - r == k * d );
            r:= r - d;
            assert(a - r - d == k * d );        
            k := k + 1;              

            var dd, c:= d + d, 1 + 1; 
            while(r >= dd)
                decreases r       
                invariant dd == c * d  
                invariant a - r == k * d 
                invariant k >= 0
                invariant r >= 0
            {
                assert(a - r == k * d );
                r:= r - dd;
                assert(a - r - dd == k * d );        
                k := k + c;            
                assert(a - r - dd == (k - c) * d );
                dd, c:= dd + dd, c + c;
                assert(a - r - dd / 2 == (k - c / 2) * d );         
                assert(a - r  == k * d - c * d /2  + dd / 2);                 
            } 
        }
        assert(r == slow_remainder(a -  k * d , d)) by {reveal slow_remainder();}      
        calc
            {
                r == slow_remainder(a -  k * d , d);          
                {congruencems2(a, d, k); } 
                r == slow_remainder(a, d);                          
            }
    }
}