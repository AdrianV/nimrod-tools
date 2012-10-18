import macros, oopHelper
      
declClass TComponent:
  var 
    FOwner* : TComponent
  method getRight(): int = 0
  proc initialize* () {.inline.} = 
    echo "init TComponent"

proc create* [T:TComponent] (AOwner: TComponent): T =
  result = T.newInstance()
  result.FOwner = AOwner
   
declClass TControl, TComponent:
  var
    FLeft, FTop, FWidth, FHeight: int
  method getRight(): int {.override.} = 
    return self.FLeft + self.FWidth
  method Foo(a, b, c: int): int =
    return a + b + c
  proc initialize () {.inline.} =
    echo "init TControl"
    initialize(super(self))
    self.FLeft = 0
    self.FTop = 0
    self.FWidth = 100
    self.FHeight = 50
  

declClass TWinControl, TControl:
  var
    FHandle : int
    Name* : string
  method Foo(a: int, b: int, c: int): int {.override.} =
    return 2 * a + b - c
        
  proc initialize () {.inline.} =
    echo "init TWinControl"
    initialize(super(self))
    self.Name = "Nimrod"
    self.FHandle = 1234


var a = create[TComponent](nil)  
var b = create[TControl](a)

#echo a.repr
echo b.FOwner == a

var c = create[TWinControl](a)


echo c.Name, " ", c.FOwner == a

c.Name = "MyName"

echo c.getClassName, " ", 

var t: TComponent = c

echo t.getClassName(), " ", t.getRight(), " ", t of TControl, " ", a of TWinControl