import macros

type
  TClassOfTCustomObject* {.pure, inheritable.} = object
    base* : ptr TClassOfTCustomObject
    className* : cstring
  TClass* = ptr TClassOfTCustomObject
  TCustomObject* {.pure, inheritable.} = object
    class* : ptr TClassOfTCustomObject
  
template assignPointer* (rhs, lhs: expr) =
  cast[ptr Pointer](addr rhs)[] = cast[Pointer](lhs)
  
template getClassPtr* (self: ref TCustomObject): TClass =
  self.class  
template getBaseClass* (self: ref TCustomObject): TClass =
  getClassPtr(self).base 
template getClassName* (self: ref TCustomObject): string =
  $getClassPtr(self).className 

template inherited*(): expr = inherited(self)
 
proc initialize* (self: ref TCustomObject) {.inline.} = nil


proc newInstance* (T: typedesc): T =
  mixin class_initialize, initialize
  #new(result)
  class_initialize(result)
  initialize(result)


  
proc isObj(x, y: TClass) : TClass {.noinit.} =
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

proc insert(father: PNimrodNode, indx: int, children: varargs[PNimrodNode]): PNimrodNode  {.compiletime.} =
  if indx >= father.len:
    father.add(children)
  else :
    var save: seq[PNimrodNode] = @[]
    for i in indx .. father.len - 1:
      save.add(father[i])
    father.del(indx, father.len - indx)
    father.add(children)
    for i in 0.. save.len-1 :
      father.add(save[i])
  return father
  
proc newPostfixIdent(name: string): PNimrodNode {.compiletime.} =
  result = newNimNode(nnkPostfix).append([
    newIdentNode("*"),
    newIdentNode(name)])
  
proc idxOfForwardPragma(node: PNimrodNode): int {.compiletime.} =
  if node.kind == nnkProcDef :
    for i in 0.. node[4].len -1 :
      if node[4][i].ident == !"forward" : return i
  return -1

proc forAll(node: PNimrodNode, call: proc(n: PNimrodNode) {.nimcall.} )  {.compiletime.} =
  for i in 0 .. node.len -1:
    if node[i] != nil :
      if node[i].len == 0: call(node[i])
      else : forAll(node[i], call)
    
proc changeSelfToResult(n: PNimrodNode)  {.compiletime.} =
  if n.kind == nnkIdent and n.ident == !"self": 
    n.ident = !"result" 
                 
proc makeConstructor(node: PNimrodNode, clsName: string): PNimrodNode {.compiletime.} =
  result = node
  if result[0].kind == nnkIdent : result[0] = newNimNode(nnkPostfix).append([newIdentNode("*"), result[0]])
  result[2] = newNimNode(nnkGenericParams).append(newNimNode(nnkIdentDefs).append([newIdentNode("T"), newIdentNode(clsName), newNimNode(nnkEmpty)]))
  result[3][0] = newIdentNode("T")
  result[3][1][1].ident = !"T"
  result[4][0].ident = !"discardable" 
  
  forAll(result[6], changeSelfToResult)
  var stm = newNimNode(nnkStmtList)
  stm.add(parseStmt("result = if self == nil: T.newInstance() else: self"))
  for i in 0..result[6].len -1:
    stm.add(result[6][i])
  result[6] = stm
        
macro declClass* (cls, base : expr) : stmt {.immediate.} =
    type
      TProcDef = tuple
        name: string
        def: PNimrodNode
        override: Bool
        destructor: Bool
    let clsbase = callsite()
    if cls.kind not_in {nnkIdent} : error "Identifier expected instead of " & cls.repr
    #expectKind(cls, nnkIdent)
    var stm = clsbase[2]
    var baseName: string = ""
    if stm.kind == nnkIdent : 
      baseName = $stm.ident
      stm = clsbase[3]
    expectKind(stm, nnkStmtList)
    result = newNimNode(nnkStmtList)
    let clsName = cls.repr
    # echo("base = " & baseName & ", type = " & clsName)
    var procs : seq[TProcDef] = @[]
    var normalProcs: seq[PNimrodNode] = @[]
    var recs = newNimNode(nnkRecList)
    for n in 0 .. stm.len -1:
      var rec = stm[n]
      if rec.kind == nnkVarSection : 
        for f in 0 .. rec.len -1 : 
          recs.add(rec[f])
      elif rec.kind == nnkProcDef or rec.kind == nnkMethodDef or rec.kind == nnkTemplateDef:
        var pname = case rec[0].kind:
          of nnkIdent : $rec[0].ident
          of nnkPostfix:  $rec[0][1].ident
          else : ""
        var over = (rec[4].kind == nnkPragma and rec[4][0].ident == !"override") #or !pname == !"destroy"
        var isDestructor = !pname == !"destroy"
        if over or rec.kind == nnkMethodDef or isDestructor:
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
          #echo params.repr
        var isConstructor = rec[4].kind == nnkPragma and rec[4][0].ident == !"constructor"
        if  isConstructor: # add constructor semantics
          rec = makeConstructor(rec, clsName)
        if over or rec.kind == nnkMethodDef or isDestructor:
          procs.add((pname, rec, over, isDestructor))
        else :
          normalProcs.add(rec)
          if isConstructor :
            var callParam = newNimNode(nnkCall).append([newNimNode(nnkBracketExpr).append([newIdentNode(pname), newIdentNode("T")]),
              newIdentNode("result")])
            #echo p.def[3].len, " " ,p.def[3].repr
            for i in 2 .. rec[3].len -1 :
              for k in 0 .. rec[3][i].len -3 :
                callParam.add(rec[3][i][k])
            #echo "param: ",callParam.repr
            
            #echo p.def[3][0].kind
            var tdef = newNimNode(nnkProcDef).append([
              rec[0],
              newNimNode(nnkEmpty),
              newNimNode(nnkEmpty),
              rec[3].copyNimTree(), 
              newNimNode(nnkPragma).append(newIdentNode("inline")),
              newNimNode(nnkEmpty),
              newNimNode(nnkAsgn).append([newIdentNode("result"), callParam])
              ])
            tdef[3][0] = newIdentNode("T")
            tdef[3][1][0] = newIdentNode("T")
            tdef[3][1][1] = newNimNode(nnkBracketExpr).append([newIdentNode("typedesc"), newIdentNode(clsName)])
            #echo tdef.repr
            normalprocs.add(tdef)          
          #echo rec.repr
    when defined(debug):
      echo procs.repr
    #echo normalProcs.repr
    # start 'type' section
    var tsection = newNimNode(nnkTypeSection)
    result.add(tsection)
    block:
      var tnode = newNimNode(nnkTypeDef)
      tnode = newNimNode(nnkTypeDef)
      tnode.add(newPostfixIdent("TClassOf"&clsName))
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
            newPostfixIdent(p.name),
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
      tnode.add(newPostfixIdent(clsName))
      
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
    echo result.repr
    result.add(parseStmt("var ClassOf" & clsName & "* : ptr TClassOf" & clsName))
    result.add(parseStmt("template getClass* (self: " & clsName & "): ptr TClassOf" & clsName & " =  cast[ptr TClassOf" & clsName & "](getClassPtr(self))"))
    if baseName != "" :
      result.add( parseStmt("template super(self:" & clsName & "):" & baseName & " = self" ))
      result.add( parseStmt("template Inherited* (self: " & clsName & "): ptr TClassOf" & baseName & " = ClassOf" & baseName))
    
    # adding proc headers first
    for i in 0 .. normalProcs.len -1 :
      var node = normalProcs[i]
      var ipragma = node.idxOfForwardPragma()
      if ipragma >= 0 :
        node[4].del(ipragma)
        if node[4].len == 0:
          node[4] = newNimNode(nnkEmpty)
        #echo node.repr
        var pheader = newNimNode(nnkProcDef).append([node[0],
          newNimNode(nnkEmpty),
          newNimNode(nnkEmpty),
          node[3],
          node[4],
          newNimNode(nnkEmpty),
          newNimNode(nnkEmpty)
          ])
        normalProcs[i][4] = newNimNode(nnkEmpty) # clear pragma
        result.add(pheader)
        #echo pheader.repr
    for p in procs :
      if p.destructor : continue
      var callParam = newNimNode(nnkCall).append(
        newNimNode(nnkDotExpr).append([newNimNode(nnkCall).append([newIdentNode("getClass"), p.def[3][1][0]]), newIdentNode(p.name)]))
      #echo p.def[3].len, " " ,p.def[3].repr
      for i in 1 .. p.def[3].len -1 :
        for k in 0 .. p.def[3][i].len -3 :
          callParam.add(p.def[3][i][k])
      #echo "param: ",callParam.repr
      
      #echo p.def[3][0].kind
      var pdef = newNimNode(nnkProcDef).append([
        p.def[0],
        newNimNode(nnkEmpty),
        newNimNode(nnkEmpty),
        p.def[3], 
        newNimNode(nnkPragma).append(newIdentNode("inline") ) ,
        newNimNode(nnkEmpty),
        newNimNode(nnkStmtList).append(if p.def[3][0].kind != nnkEmpty : newNimNode(nnkReturnStmt).append(callParam) else : callParam)
        ])
      #echo "proc = ", pdef.repr
      result.add(pdef)
    var sdestroy = "TClassOf" & clsName & "_destroy"
    result.add(parseStmt("template class_initialize* (self: "&clsName&") =\n  when compiles("&sdestroy&"(self)): new(self, "&sdestroy&" ) else : new(self)\n  self.class = cast[ptr TClassOf"&clsName&"](ClassOf"&clsName&")"))
    for i in 0 .. normalProcs.len -1 :
      #echo normalProcs[i].repr
      result.add(normalProcs[i])
    for p in procs :
      var sname = "TClassOf" & clsName & "_" & p.name
      var pdef = newNimNode(nnkProcDef).append(if !p.name != !"destroy" : newIdentNode(sname) else: newPostfixIdent(sname))
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
    # now adding proc boddies and templates
      
    when true or defined(debug):
      echo result.repr
