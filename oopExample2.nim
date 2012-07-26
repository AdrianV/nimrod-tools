import macros
    
macro refobjdecl(clsbase : expr) : stmt =
    result = newNimNode(nnkStmtList) 
    # for i in 1..clsbase.len-1:
    #  echo(repr(clsbase[i]))
    let tname = repr(clsbase[1])
    let baseName = repr(clsbase[2])
    # echo("base = " & baseName & ", type = " & tname)
    let fields = clsbase[3][0] # [0] skip stmt list
        
    # echo("fields = " & repr(fields))

    # start 'type' section
    var tsection = newNimNode(nnkTypeSection)
    result.add(tsection)
    
    block:
        # define 'type' node for Tclass * = ref object base
        var tnode = newNimNode(nnkTypeDef)
        tsection.add(tnode)
        
        # define type name with * operator
        var tpostf = newNimNode(nnkPostfix)
        tpostf.add(newIdentNode("*"))
        tpostf.add(newIdentNode(tname))
        tnode.add(tpostf)
        
        # reference to the code - here nil
        tnode.add(newNimNode(nnkEmpty))
        
        # the actual type = ref object
        var reft = newNimNode(nnkRefTy)
        var objt = newNimNode(nnkObjectTy)
        reft.add(objt)
        tnode.add(reft)
        # again reference to code I guess
        objt.add(newNimNode(nnkEmpty))
        
        var inh = newNimNode(nnkOfInherit)
        objt.add(inh)
        inh.add(newIdentNode(baseName))
        # echo("tree = ", lispRepr(inh))    
        
        var recs = newNimNode(nnkRecList)
        objt.add(recs)

        for f in 0 .. fields.len -1 : 
          recs.add(fields[f])
             
    # echo("tree = ", lispRepr(tsection))
    
template declClass* (clsName : expr, baseCls : expr, fields : stmt) : stmt = 
  bind refobjdecl        
  
  refobjdecl(clsName, baseCls, fields)

  proc super* (me: `clsName`): baseCls {.inline.} = return me
    

type
  TComponent* = ref object
    FOwner* : TComponent

proc create* [T:TComponent] (AOwner: TComponent): T =
  new(Result)
  initialize(Result, AOwner)

proc initialize* (me: TComponent, AOwner: TComponent) {.inline.} = # initialize* has to be declared public (with *) !!
  echo "init TComponent"
  me.FOwner = AOwner
   
declClass TControl, TComponent:
  var
    FLeft, FTop, FWidth, FHeight: int

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

proc initialize* (me: TWinControl, AOwner: TComponent) {.inline.} =
  echo "init TWinControl"
  initialize(super(me), AOwner)
  me.Name = "Nimrod"
  me.FHandle = 1234

when isMainModule:
  
  var a = create[TComponent](nil)  
  var b = create[TControl](a)
      
  echo a.repr
  echo b.repr    

  echo b.FOwner == a

  var c = create[TWinControl](a)

  echo c.Name, " ", c.FOwner == a

  c.Name = "MyName"
