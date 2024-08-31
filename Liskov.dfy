
trait IRectangle
{
  method SetX(Newx: nat)
  modifies this
  ensures Newx == Width()
  ensures old(Height()) == Height()
  method SetY(Newy: nat)
  modifies this
  ensures Newy == Height()
  ensures old(Width()) == Width()  
  function Width(): nat
      reads this
  function Height(): nat
      reads this  
}

trait ISquare extends IRectangle
{
   predicate Valid()
    reads this  
  {
     Width() == Height()
  }
}

class Rectangle extends IRectangle
{
  var x: nat, y: nat
  method SetX(Newx: nat)
  modifies this
  ensures Newx == Width()
  ensures old(Height()) == Height()  
  {
    x := Newx;
  }
  method SetY(Newy: nat)
  modifies this
  ensures Newy == Height()
  ensures old(Width()) == Width()    
  {
    y := Newy;
  }  
   function Width() : nat
   reads this
  {
    x
  }  
   function Height() : nat
   reads this
  {
    y
  } 
}

// class Square extends ISquare
// {
//    var x: nat     
//   method SetX(Newx: nat)
//   modifies this
//   ensures Newx == Width()
//   ensures old(Height()) == Height()    
//   {
//     x := Newx;
//   }
//   method SetY(Newy: nat)
//   modifies this
//   ensures Newy == Height()
//   ensures old(Width()) == Width()      
//   {
//     x := Newy;
//   } 
//    function Height() : nat
//    reads this
//   {
//     x
//   }
//   function Width() : nat
//    reads this
//   {
//     x
//   }
// }

method TestRectangle(Rect: IRectangle)
modifies Rect
{ 
    Rect.SetX(10);
    Rect.SetY(20);    
    assert(Rect.Height() == 20 && Rect.Width() == 10);
}

method TestSquare(Square: ISquare)
modifies Square
{  
    Square.SetX(10);
    Square.SetY(20);   
    assert(Square.Height() == 20 && Square.Width() == 10);
    assert(!Square.Valid());
}

method TestBox()
{
    var myShapes: seq<IRectangle>;
    var A := new Rectangle;
    var B := new Square; // Square is a subtype of Rectangle
    myShapes := [A, B];
}

type Arrow<-X, +Y> = X -> Y

function absfunc(x: int) : nat
{
  if (x > 0) then x else -x
}

function testfunc(x: nat) : int
{
  x
}

method TestCoAndCotraVariance()
{
  // nat is a subtype of int
  // Arrow<A, nat> is a subtype of Arrow<A, int>
  // Arrow<int, A> is a subtype of Arrow<nat, A>
  // Arrow<int, nat> is a subtype of Arrow<nat, int>
  var funvariable: Arrow<nat, int> := absfunc;
  var funvariable2: Arrow<int, nat> := absfunc;
  var funvariable3: Arrow<nat, int> := testfunc;
  //var funvariable4: Arrow<int, nat> := testfunc;
}