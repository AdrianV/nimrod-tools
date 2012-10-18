import macros

type
  TClassOfTCustomObject* {.pure, inheritable.} = object
    base* : ptr TClassOfTCustomObject
    className* : cstring
  TCustomObject* {.pure, inheritable.} = object
    class* : ptr TClassOfTCustomObject
  
template assignPointer* (rhs, lhs: expr) =
  cast[ptr Pointer](addr rhs)[] = cast[Pointer](lhs)
  
template getClassPtr* (self: ref TCustomObject): ptr TClassOfTCustomObject =
  self.class  
template getBaseClass* (self: ref TCustomObject): ptr TClassOfTCustomObject =
  getClassPtr(self).base 
template getClassName* (self: ref TCustomObject): string =
  $getClassPtr(self).className 

template inherited*(): expr = inherited(self)
 
proc initialize* (self: ref TCustomObject) {.inline.} = nil

proc newInstance* (T: typedesc): T =
  mixin class_initialize, initialize
  new(result)
  class_initialize(result)
  initialize(result)

proc isObj(x, y: ptr TClassOfTCustomObject) : ptr TClassOfTCustomObject {.noinit.} =
  result = x
  if result == y : return
  result = result.base
  while true :
    if result == y : return 
    if result == nil : return 
    result = result.base
  
template `??` * (x: ref TCustomObject, y: typedesc): bool =
  bind isObj
  (not isNil(x) and not IsNil(isObj(x.class, `ClassOf y`)))
  #(not isNil(x) and (x.class == `ClassOf y` or isObj(x.class.base, `ClassOf y`)))
    
template ofRewrite* {`of`(x, y)}(x: ref TCustomObject, y: typedesc): bool = x ?? y

macro dump* (): stmt  {.immediate.} =
  let n = callsite()
  echo n.lisprepr
  
proc append(father, child: PNimrodNode): PNimrodNode  {.compiletime.} =
  father.add(child)
  return father

proc append(father: PNimrodNode, children: varargs[PNimrodNode]): PNimrodNode  {.compiletime.} =
  father.add(children)
  return father
  
proc newExportIdent(name: string): PNimrodNode {.compiletime.} =
  result = newNimNode(nnkPostfix).append([
    newIdentNode("*"),
    newIdentNode(name)])
  
macro declClass* (cls, base : expr) : stmt {.immediate.} =
    type
      TProcDef = tuple
        name: string
        def: PNimrodNode
        override: Bool
    let clsbase = callsite()
    expectKind(cls, nnkIdent)
    var stm = clsbase[2]
    var baseName: string = ""
    if stm.kind == nnkIdent : 
      baseName = $stm.ident
      stm = clsbase[3]
    expectKind(stm, nnkStmtList)
    result = newNimNode(nnkStmtList)
    let clsName = $cls.ident
    # echo("base = " & baseName & ", type = " & clsName)
    var procs : seq[TProcDef] = @[]
    var normalProcs: seq[PNimrodNode] = @[]
    var recs = newNimNode(nnkRecList)
    for n in 0 .. stm.len -1:
      let rec = stm[n]
      if rec.kind == nnkVarSection : 
        for f in 0 .. rec.len -1 : 
          recs.add(rec[f])
      elif rec.kind == nnkProcDef or rec.kind == nnkMethodDef:
        var pname = case rec[0].kind:
          of nnkIdent : $rec[0].ident
          of nnkPostfix:  $rec[0][1].ident
          else : ""
        var over = rec[4].kind == nnkPragma and rec[4][0].ident == !"override"
        if over or rec.kind == nnkMethodDef :
          rec[4] = newNimNode(nnkEmpty)
        if rec[3].len > 1 and rec[3][1][0].ident == !"self" : # has self
          if rec[3][1][1].ident != !clsName:
            rec[3][1][1] = newIdentNode(clsName) # force right class
        else:
          var params = newNimNode(nnkFormalParams).append([rec[3][0],
            newNimNode(nnkIdentDefs).append([newIdentNode("self"), 
              newIdentNode(clsName),
              newNimNode(nnkEmpty)
              ]) 
            ])
          for i in 1 .. rec[3].len -1 :
            params.add(rec[3][i])
          rec[3] = params
          echo params.repr
        if over or rec.kind == nnkMethodDef :
          procs.add((pname, rec, over))
        else :
          normalProcs.add(rec)
    when defined(debug):
      echo procs.repr

    # start 'type' section
    var tsection = newNimNode(nnkTypeSection)
    result.add(tsection)
    block:
      var tnode = newNimNode(nnkTypeDef)
      tnode = newNimNode(nnkTypeDef)
      tnode.add(newExportIdent("TClassOf"&clsName))
      tnode.add(newNimNode(nnkEmpty))
      
      # the actual type = ref object
      var objt = newNimNode(nnkObjectTy)
      tnode.add(objt)
    
      objt.add([newNimNode(nnkEmpty),
        newNimNode(nnkOfInherit).append(newIdentNode("TClassOf" & (if baseName != "" : baseName else : "TCustomObject")))])
      
      var recList = newNimNode(nnkRecList)
      if procs.len > 0:
        for p in procs:
          if p.override : continue
          recList.add(newNimNode(nnkIdentDefs).append([
            newExportIdent(p.name),
            newNimNode(nnkProcTy).append([p.def[3], newNimNode(nnkPragma).append(newIdentNode("nimcall"))]),
            newNimNode(nnkEmpty)
            ]))
      else :
        recList.add(nil)
      objt.add(recList)
      #echo tnode.repr
      tsection.add(tnode)
      
    block:
      # define 'type' node for Tclass * = ref object base
      var tnode = newNimNode(nnkTypeDef)
      
      # define type name with * operator
      tnode.add(newExportIdent(clsName))
      
      # reference to the code - here nil
      tnode.add(newNimNode(nnkEmpty))
      
      # the actual type = ref object
      var objt = newNimNode(nnkObjectTy)
      tnode.add(newNimNode(nnkRefTy).append(objt))
    
      objt.add([newNimNode(nnkEmpty),
        newNimNode(nnkOfInherit).append(newIdentNode(if baseName != "" : baseName else : "TCustomObject"))])
      when false:
        objt.add([ newNimNode(nnkPragma).append(newIdentNode("inheritable")),
          newNimNode(nnkEmpty)])
      
      objt.add(recs)
      #echo tnode.repr
      tsection.add(tnode)

    #echo tsection.repr
    result.add(parseStmt("var ClassOf" & clsName & "* : ptr TClassOf" & clsName))
    result.add(parseStmt("template getClass* (self: " & clsName & "): ptr TClassOf" & clsName & " =  cast[ptr TClassOf" & clsName & "](getClassPtr(self))"))
    result.add(parseStmt("proc class_initialize* (self: "&clsName&") {.inline.} = self.class = cast[ptr TClassOf"&clsName&"](ClassOf"&clsName&")"))
    if baseName != "" :
      result.add( parseStmt("template super(self:" & clsName & "):" & baseName & " = self" ))
      result.add( parseStmt("template Inherited* (self: " & clsName & "): ptr TClassOf" & baseName & " = ClassOf" & baseName))

    for p in procs :
      var callParam = newNimNode(nnkCall).append(
        newNimNode(nnkDotExpr).append([newNimNode(nnkCall).append([newIdentNode("getClass"), p.def[3][1][0]]), newIdentNode(p.name)]))
      echo p.def[3].len, " " ,p.def[3].repr
      for i in 1 .. p.def[3].len -1 :
        for k in 0 .. p.def[3][i].len -3 :
          callParam.add(p.def[3][i][k])
      echo "param: ",callParam.repr
      var pdef = newNimNode(nnkProcDef).append([
        p.def[0],
        newNimNode(nnkEmpty),
        newNimNode(nnkEmpty),
        p.def[3], 
        newNimNode(nnkPragma).append(newIdentNode("inline")),
        newNimNode(nnkEmpty),
        newNimNode(nnkStmtList).append(newNimNode(nnkReturnStmt).append(callParam))
        ])
      #echo "proc = ", pdef.repr
      result.add(pdef)
    for p in procs :
      var pdef = newNimNode(nnkProcDef).append(newIdentNode("TClassOf" & clsName & "_" & p.name))
      for d in 1 .. p.def.len -1 :
        pdef.add(p.def[d])
      #echo pdef.repr
      result.add(pdef)
    block:
      var stm = newNimNode(nnkStmtList)
      var pdef = newNimNode(nnkProcDef).append([
        newIdentNode("initTClassOf" & clsName),
        newNimNode(nnkEmpty),
        newNimNode(nnkEmpty),
        newNimNode(nnkFormalParams).append(newNimNode(nnkEmpty)), # params 
        newNimNode(nnkEmpty), # pragma
        newNimNode(nnkEmpty),
        stm
        ])
      stm.add([
        parseStmt("var class {.global.}: TClassOf" & clsName),
        parseStmt("ClassOf" & clsName &" = addr class")
        ])
      if baseName != "" :
        stm.add([parseStmt("copyMem(ClassOf" & clsName & ", ClassOf" &baseName& ", sizeof(TClassOf"&baseName&"))"),
          parseStmt("assignPointer(ClassOf" & clsName & ".base, ClassOf" & baseName &")")
          ])
      stm.add(parseStmt("ClassOf"&clsName&".className = \""& clsName & "\""))
      for p in procs:
        stm.add(parseStmt("assignPointer(ClassOf"&clsName&"."&p.name&", TClassOf"&clsName&"_"&p.name&")"))  
      #echo pdef.repr
      result.add(pdef)
    result.add(parseStmt("initTClassOf" & clsName &"()"))
    for p in normalProcs: result.add(p)
    when defined(debug):
      echo result.repr
