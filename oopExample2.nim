import macros, oopHelper
      
declClass TComponent:
  var 
    FOwner* : TComponent
  proc getRight(self: TComponent): int = 0

proc create* [T:TComponent] (AOwner: TComponent): T =
  mixin initialize, class_initialize
  new(Result)
  class_initialize(Result)
  initialize(Result, AOwner)

proc initialize* (me: TComponent, AOwner: TComponent) {.inline.} = # initialize* has to be declared public (with *) !!
  echo "init TComponent"
  me.FOwner = AOwner
  
   
declClass TControl, TComponent:
  var
    FLeft, FTop, FWidth, FHeight: int
  proc getRight(self: TControl): int {.override.} = 
    return self.FLeft + self.FWidth
  proc Foo(self: TControl, a: int, b: int, c: int): int =
    return a + b + c
      
proc initialize* (me: TControl, AOwner: TComponent) {.inline.} =
  echo "init TControl"
  initialize(super(me), AOwner)
  me.FLeft = 0
  me.FTop = 0
  me.FWidth = 100
  me.FHeight = 50
  

declClass TWinControl, TControl:
  var
    FHandle : int
    Name* : string
  proc Foo(self: TWinControl, a: int, b: int, c: int): int {.override.} =
    return 2 * a + b - c
    
proc initialize* (me: TWinControl, AOwner: TComponent) {.inline.} =
  echo "init TWinControl"
  initialize(super(me), AOwner)
  me.Name = "Nimrod"
  me.FHandle = 1234


var a = create[TComponent](nil)  
var b = create[TControl](a)

echo b.FOwner == a

var c = create[TWinControl](a)


echo c.Name, " ", c.FOwner == a

c.Name = "MyName"

echo c.getClassName, " ", 

var t: TComponent = c

echo t.getClassName(), " ", t.getRight()