opaque function slow_remainder(x: int, n: nat): (int)
    requires n > 0
    decreases x
{
    if x < n then 
        x
    else 
        slow_remainder(x - n, n)
}

lemma Assocc(x: int, y: int, n: int)
  requires n: n > 0
  ensures (x - y) % n == (x % n - y % n) % n
  

lemma ModuloHelper0(x: int, n: int)
requires n > 0
requires n > x >= 0
ensures x % n == x
{

}

lemma ModuloHelper1(x: int, n: int)
requires n > x >= 0
ensures (x - n) % n == x
{

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

 lemma congruencem(a: int, b: int)
    requires b > 0
     ensures a % b == (a - b) % b
 {
    assert(a == a / b * b + a % b);
    var y := a - b;
    assert(y ==  y / b * b +  y % b);    
    assert(0 <= a % b < b);
    assert(0 <= y % b < b);    
    assert(-b < a % b - y % b < b); 
    assert(a % b - y % b == a - y - a / b * b + y / b * b);  
    assert(a % b - y % b == b - a / b * b + y / b * b);   
    assert(a % b - y % b == b * (1- a / b + y / b));  
    assert(-b < b * (1- a / b + y / b) < b);
    assert(false);
    assert(-1 < (1- a / b + y / b) < 1);    
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