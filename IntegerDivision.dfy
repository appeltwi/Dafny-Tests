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
    requires b > 0
    ensures k >= 0
    ensures r == pow(2, k) * b
    ensures r <= a < 2 * r 
{
    r := b;
    k := 0;
    assert( pow(2, k) * b == r)  by { reveal pow(); }
    while (a >= 2 * r)
        invariant r == pow(2, k) * b
        invariant a >= r
    {
        reveal pow();
        r, k := 2 * r, k + 1;      
    }
}

lemma congruencems2(a: int, b: int, k: int)
 requires k > 0
 requires b > 0
 requires a >= k *b + b
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

 lemma AssociativityLaw(x: int, n: int, m: int)
  requires npos: n >= 0
  requires mpos: m >= 0
  ensures pow(x, n + m) == pow(x, n) * pow(x, m)
{	  
    if (m == 0)
    {
        reveal npos;
        assert(pow(x, n + 0) == pow(x,n) * pow(x, 0)) by 
        {
            reveal pow();
        }
    } 
    else
    {
        reveal npos; 
        reveal mpos;        
        calc 
        {                                
            pow(x, n + m);                
            pow(x, n + m - 1 + 1);            
            { reveal pow(); }
            pow(x, n + m - 1) * x;  
            { AssociativityLaw(x, n, m - 1);}
            pow(x, n) * pow(x, m - 1) * x;   
            { reveal pow(); }
            pow(x, n) * pow(x, m);                   
        }
    }
}

method remainder_recursive(a: int, b: int) returns (r: int)
 requires a >= b
 requires b > 0
 decreases a - 2*b
{
    r:= a;
    if (r >= 2 * b)
    {
        r:= remainder_recursive(r, 2 *b);     
        if (r >= b)
        {
            r:= r- b;
        }
    }
    else
    {
        r:= r-b;
    }
    return r;
}

method fast_remainder(a: int, b: int) returns (r: int)
    requires a >= 0
    requires b > 0
    ensures r == slow_remainder(a, b)
{
    if (a < b)
    {
        r:= a;
        assert(r == slow_remainder(a, b)) by {reveal slow_remainder();}        
    }
    else // a >= b
    {
        var c, k := largest_doubling(a, b);
        assert(c == pow(2, k) * b);          
        assert(c <= a < 2 * c );             
        r := a - c; 
        assert(r == a - pow(2, k) * b);
        assert(0 <= r < c );         
        assert(r == slow_remainder(a, c)) by {reveal slow_remainder();}   
        assert(r == slow_remainder(r, c)) by {reveal slow_remainder();}      
        assert(slow_remainder(a, c) == slow_remainder(r, c));                     
        while(k > 0)
            decreases k 
            invariant c == pow(2, k) * b
            invariant c > 0
            invariant r == slow_remainder(r, c)
            invariant slow_remainder(r, c) == slow_remainder(a, c)
            invariant 0 <= r < c  
        {   
            assert(c / 2 == pow(2, k - 1) * b) by {reveal pow(); AssociativityLaw(2, k -1 , 1);}  
            assert(c / 2 + c / 2 == c) by {reveal pow();}  
            c, k := c / 2, k -1;
            if (c > r)
            {     
                assert(slow_remainder(r, c) == r )by {reveal slow_remainder();}                       
            }
            else 
            {
                r := r - c;
                assert(slow_remainder(r, c) == r) by {reveal slow_remainder();}  
            }              
        }
        assert(k == 0);
        assert(c == pow(2, k) * b) by {reveal pow();}   
        assert(pow(2, 0) == 1 )  by {reveal pow();}   
        assert(c == b);
        assert(r == slow_remainder(a, b));
    }
}