#
#                  nimrod-tools
#        (c) Copyright 2013 Adrian Veith
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## This module implements a macro for generating Object Pascal
## like inheritance with a VMT

import macros, macroHelper, algorithm

type
  TClassOfTCustomObject* {.pure, inheritable.} = object
    base* : ptr TClassOfTCustomObject
    className* : cstring
    init: proc()
  TClass* = ptr TClassOfTCustomObject
  TCustomObject*  = ref object {.pure, inheritable.}
    class* : ptr TClassOfTCustomObject
  
template assignPointer* (lhs, rhs: expr) =
  cast[ptr Pointer](addr lhs)[] = cast[Pointer](rhs)
  
template getClassPtr* (self: TCustomObject): TClass =
  self.class  
template getBaseClass* (self:  TCustomObject): TClass =
  getClassPtr(self).base 
template getClassName* (self: TCustomObject): string =
  $getClassPtr(self).className 

template inherited*(): expr = inherited(self)
 
template initialize* (self: TCustomObject) = discard

var ClassOfTCustomObject* = TClassOfTCustomObject(className: "TCustomObject")

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
  
template `??` * (x: TCustomObject, y: typedesc): bool =
  bind isObj
  (not isNil(x) and not IsNil(isObj(x.class, addr `ClassOf y`)))
  #(not isNil(x) and (x.class == `ClassOf y` or isObj(x.class.base, `ClassOf y`)))
    
template ofRewrite* {`of`(x, y)}(x: TCustomObject, y: typedesc): bool = x ?? y


template mkConstructor1(cls, con, code: expr) : stmt {.dirty.} =
  proc `con`* (self: `cls`): `cls` {.discardable.} =
    result = self
    code

template mkConstructor2(cls, con: expr) : stmt {.dirty.} =
  template `con`* (T: typedesc[`cls`]): expr =
    cast[T](`con`(T.newInstance()))
   
template mkVProcType(name: expr): stmt {.dirty.} =
  var `name`* : proc() {.nimcall.}

template mkVProcImpl(cls, name: expr): stmt {.dirty.} =
  template `name` () = getClass(self).`name`()
  
  
template typeDefClassOf(cls, base: expr) :  stmt {.dirty.} =
  type
    `TClassOf cls`* = object of `TClassOf base`
      nil
      
template typeDefClass(cls, base: expr) :  stmt {.dirty.} =
  type
    `cls`* = ref object of `base`
      nil

        
template implClassOf(cls, base: expr) :  stmt {.dirty.} =
  var 
    `ClassOf cls` *: `TClassOf cls`
  template getClass*(self: `cls`): ptr `TClassOf cls` =
      cast[ptr `TClassOf cls`](getClassPtr(self))  

  template super(self: `cls` ): `base` = cast[`base`](self)
  template inherited* (self: `cls` ): ptr `TClassOf base` = addr `ClassOf base`
  template class_initialize*(self: `cls`) =
    when compiles(destroy(self)):
      new(self, `TClassOf cls destroy`)
    else:
      new(self)
    self.class = cast[ptr `TClassOf cls`](addr `ClassOf cls`)
        
template mkClassOfInit(cls, baseCls: expr, name: string, body: expr) :  stmt {.dirty.} =
  when compiles(destroy(self)):
    proc `TClassOf cls destroy` (self: `cls`) {.nimcall.} =
      destroy(self)

  `ClassOf cls`.init = proc() =
    when compiles(`ClassOf baseCls`) :
      `TClassOf baseCls`(`ClassOf cls`) = `ClassOf baseCls` 
      `ClassOf cls`.base = addr `ClassOf baseCls`
    `ClassOf cls`.className = name
    body
  `ClassOf cls`.init()
    
template mkVProcAssign(cls, name, body: expr): stmt {.dirty.} =
  `ClassOf cls`.`name` = cast[`ClassOf cls`.`name`.type] ( proc() =
      body
     )

type
  TProcDef = tuple
    name: string
    def: PNimrodNode
    override: Bool
    destructor: Bool
    constructor: Bool
    condef: PnimrodNode
  TCollectInfo = tuple
    procs: seq[TProcDef]
    normalProcs: seq[PNimrodNode]
    recs: PNimrodNode
  TTypeNodeInfo = object
    node: PNimrodNode
    stmtNr: Int
    nodeNr: Int
  TClassDef = ref object
    pre: TTypeNodeInfo
    clsName: string
    cls: PNimrodNode
    base: PNimrodNode
    clsInfo: TCollectInfo
    stmtNr: Int
    
proc collectClassInfo(stm: PNimrodNode; def: TClassDef; clsInfo: var TCollectInfo) {.compiletime.} =
  clsInfo.procs = @[]
  clsInfo.normalProcs = @[]
  clsInfo.recs = newNimNode(nnkRecList)
  var selfParam = newNimNode(nnkIdentDefs).add(newIdentNode("self")).add(newIdentNode(def.clsName)).add(newNimNode(nnkEmpty))
  for n in 0 .. stm.len -1:
    var rec = stm[n]
    if rec.kind == nnkVarSection : 
      for f in 0 .. rec.len -1 : 
        clsInfo.recs.add(rec[f])
    elif rec.kind == nnkProcDef or rec.kind == nnkMethodDef or rec.kind == nnkTemplateDef:
      var pname = rec[pdIdent].fullIdent
      var over = (rec[4].kind == nnkPragma and rec[4][0].ident == !"override") #or !pname == !"destroy"
      var isConstructor = rec[4].kind == nnkPragma and rec[4][0].ident == !"constructor"
      var isDestructor = !pname == !"destroy"
       
      if not isConstructor and (over or rec.kind == nnkMethodDef or isDestructor):
        rec[4] = newNimNode(nnkEmpty)
      if rec[3].len > 1 and rec[3][1][0].ident == !"self" : # has self
        if rec[3][1][1].ident != !def.clsName:
          rec[3][1][1] = newIdentNode(def.clsName) # force right class
      else:
        rec.params= rec.params.insert(1, [selfParam]) 
      var conDef: PNimrodNode  
      if isConstructor: # add constructor semantics
        var node = getAst(mkConstructor1(def.cls, newIdentNode(pname), rec[pdBody]))[0]
        node.params= node.params.insert(2, rec.paramsRange(2, -1))
        rec = node
        # echo rec.repr
      if over or rec.kind == nnkMethodDef or isDestructor:
        def.clsInfo.procs.add((pname, rec, over, isDestructor, isConstructor, conDef))
      else :
        def.clsInfo.normalProcs.add(rec)
        if isConstructor :
          var node = getAst(mkConstructor2(def.cls, newIdentNode(pname)))[0]
          #echo node.treeRepr
          node[pdFormalParams] = node[pdFormalParams].insert(2, rec.paramsRange(2, -1))
          node[pdBody][0][1].add(node.paramsIdentRange(2, -1))
          def.clsInfo.normalProcs.add(node)
          # echo node.repr

proc genVMTRecList(clsInfo: var TCollectInfo): PNimrodNode {.compiletime.} =
  result = newNimNode(nnkRecList)
  for p in clsInfo.procs:
    if p.override or p.destructor : continue
    var node = getAst(mkVProcType(newIdentNode(p.name)))[0][0]
    node[1][0] = p.def.params
    result.add(node)

proc addForwardProcs(result: var PNimrodNode; clsInfo: var TCollectInfo) {.compiletime.} =
  for i in 0 .. clsInfo.normalProcs.len -1 :
    var node = clsInfo.normalProcs[i]
    var ipragma = node.indexOfPragma("forward")
    if ipragma >= 0 :
      node.removePragma(ipragma)
      var pheader = newNimNode(nnkProcDef).add([node[0],
        node[1],
        node[2],
        node[3],
        node[4],
        node[5],
        newNimNode(nnkEmpty)
        ])
      result.add(pheader)
      clsInfo.normalProcs[i][pdPragma] = newNimNode(nnkEmpty) # clear all pragmas for implementation

proc addVirtualStubs(result: var PNimrodNode; def: TClassDef) {.compiletime.} =
  for i in 0 .. < def.clsInfo.procs.len :
    var p = def.clsInfo.procs[i]
    if p.destructor : continue
    var node = getAst(mkVProcImpl(def.cls, newIdentNode(p.name) ))
    node[0][pdFormalParams]= p.def[pdFormalParams]
    node[0][pdBody][0].add(p.def.paramsIdentRange(1,-1))
    result.add(node)
  
proc addClassOfInit(result: var PNimrodNode; def: TClassDef) {.compiletime.} =
  var pinit = newNimNode(nnkStmtList)
  for p in def.clsInfo.procs :
    var call = getAst(mkVProcAssign(def.cls, newIdentNode(p.name), p.def[pdBody]))
    call[0][1][1][pdFormalParams]= p.def[pdFormalParams] 
    # echo call.treeRepr 
    pinit.add(call) 
  var node = getAst(mkClassOfInit(def.cls, def.base, def.clsName, pinit))
  result.add(node)

macro declClass* (cls, base : expr) : stmt {.immediate.} =
    let clsbase = callsite()
    if cls.kind not_in {nnkIdent} : error "Identifier expected instead of " & cls.repr
    #expectKind(cls, nnkIdent)
    if clsbase.len < 3 : error "defintion expected"
    var stm = clsbase[2]
    # echo clsbase.treeRepr
    var def: TClassDef
    new(def)
    def.cls = cls
    def.base = newIdentNode("TCustomObject")
    if stm.kind == nnkIdent : 
      def.base = stm
      if clsbase.len < 4 : error "defintion expected"
      stm = clsbase[3]
    expectKind(stm, nnkStmtList)
    def.clsName = $cls.ident
    collectClassInfo(stm, def, def.clsInfo)
    when defined(debugOOP):
      echo def.clsName, ": ", def.clsInfo.procs.repr
      echo def.clsInfo.normalProcs.repr
      # echo procs[0].name
    result = getAst(typeDefClassOf(def.cls, def.base))
    # echo result.treeRepr
    result[0][0][tdType][otRecList] = genVMTRecList(def.clsInfo) 
    # echo result.treeRepr
    let typCls = getAst(typeDefClass(def.cls, def.base))
    # echo typCls.treeRepr
    typCls[0][0][tdType][0][otRecList] = def.clsInfo.recs
    result[0].add(typCls[0][0])
    # echo result.repr
    result.add getAst(implClassOf(def.cls, def.base))
    # adding forward proc headers first
    result.addForwardProcs(def.clsInfo)
        
    # now spit out the virtual procs  
    result.addVirtualStubs(def)  
      
    # now the implementations of the normal procs
    for i in 0 .. < def.clsInfo.normalProcs.len :
      var p = def.clsInfo.normalProcs[i]
      result.add(p)
    
    # create the class initialization code
    result.addClassOfInit(def)
    when defined(debugOOP) :
      echo result.repr



var classes {.compiletime.} : seq[TClassDef] = @[]
  
proc getInherit(objType: PNimrodNode): PNimrodNode {.compiletime.} =
  if objType.kind == nnkObjectTy and objType[1].kind == nnkOfInherit: return objType[1][0]

proc getClassDef(ident: TNimrodIdent): TClassDef {.compiletime.} =
  for c in classes:
    if c.cls.ident == ident: return c  
   
proc getClsAndBase(node: PNimrodNode): tuple[cls: PNimrodNode, base: PNimrodNode] {.compiletime.} =
  if node.kind == nnkIdent : return (cls: node, base: nil)
  elif node.kind == nnkInfix and node[0].ident == !"of" : return (cls: node[1], base: node[2])

proc addNodeRange(result: var PNimrodNode; stm : PNimrodNode; a, b: Int) {.compiletime.} =
  for i in a .. < b:
    result.add(stm[i])      
  
type
  TGenWhat = enum gwType, gwImpl
  TGenInfo = ref object
    gen: set[TGenWhat]
    node: int
    def: TClassDef 
    
proc cmpGenInfo(a,b: TGenInfo): int {.compiletime.} = return cmp(a.node, b.node)
    
macro oopEnhance*(s: stmt): stmt {.immediate.} =
  classes = @[]
  # let s = callsite()
  #echo s.treeRepr
  for i in 0 .. < s.len :
    let n = s[i]
    if n.kind == nnkTypeSection :
      for it in 0 .. < n.len :
        let typ = n[it] 
        if typ.kind == nnkTypeDef and typ[0].kind == nnkPragmaExpr and typ[0][1][0].ident == !"class":   
          # echo typ.treeRepr
          typ[0] = typ[0][0]
          var def: TClassDef
          new(def)
          # echo "here ", isNil(def)
          def.pre.node = typ
          def.pre.stmtNr = i
          def.pre.nodeNr = it
          def.cls = typ[0]
          def.clsName = $def.cls.ident
          case typ[2].kind :
          of nnkRefTy : def.base = getInherit(typ[2][0])
          of nnkObjectTy : def.base = getInherit(typ[2])
          else : discard
          if isNil(def.base) : 
            def.base = newIdentNode("TCustomObject")
            case typ[2].kind :
            of nnkRefTy : 
              if typ[2][0].kind == nnkObjectTy : typ[2][0][1] = newNimNode(nnkOfInherit).add(def.base)
            of nnkObjectTy : typ[2][1] = newNimNode(nnkOfInherit).add(def.base)
            else: discard
          classes.add(def)
          # echo def.repr
    elif n.kind == nnkCall and n[0].ident == !"class" :
      # echo n[1].treeRepr    
      let cls = getClsAndBase(n[1])
      # echo "class = ", cls.repr
      var def = if cls.cls.kind == nnkIdent : getClassDef(cls.cls.ident) else : nil
      var isNew = false
      if isNil(def) and cls.cls != nil :
        isNew = true
        new(def)
        def.cls = cls.cls
        def.clsName = $cls.cls.ident
        def.base = if not isNil(cls.base) : cls.base else : newIdentNode("TCustomObject")
      if not isNil(def) :
        def.stmtNr = i
        if not isNil(cls.base) and cls.base.ident != def.base.ident : error ("class " & $cls.cls.ident & " does not match prior definition")
        collectClassInfo(n[2][doStmtList], def, def.clsInfo) 
        # echo "node ",n.treeRepr
        if isNew : classes.add(def) # argh VM 
        # echo def.clsName, " ", isNil(def.clsInfo.procs), " ", def.repr 
        # echo classes.repr
      else :
        echo n.treeRepr
        error ($n[1].ident & " is not defined")
  result = newNimNode(nnkStmtList)
  var process: seq[TGenInfo] = @[]
  var countUndef = 0
  for i in 0 .. < classes.len :
    var def = classes[i]
    # echo "def ", def.clsName, " ", isNil(def.clsInfo.procs), " ", def.repr 
    if isNil(def.clsInfo.procs) :
      echo "undefined ", def.clsName
      inc(countUndef)
      continue
    var gen: TGenInfo
    if not isNil(def.pre.node) :
      new(gen)
      gen.node = def.pre.stmtNr
      gen.gen = {gwType}
      gen.def = def
      process.add(gen)
      new(gen)
      gen.node = def.stmtNr
      gen.gen = {gwImpl}
      gen.def = def
      process.add(gen)
    else:
      new(gen)
      gen.node = def.stmtNr
      gen.gen = {gwType, gwImpl}
      gen.def = def
      process.add(gen)
  if countUndef > 0 : error ($countUndef & " undefined classes found")
  process.sort(cmpGenInfo)  
  var nodeNr = 0 
  var typNr = -1
  var stmtNr = -1
  # echo process.repr
  proc emitNodes(result: var PNimrodNode, stm: PNimrodNode, until: int) {.compiletime.} =
    if stmtNr != until :
      if stmtNr >= 0 and typNr >= 0 :
        var last = result.len -1
        var res = result[last]
        res.addNodeRange(stm[stmtNr], typNr, stm[stmtNr].len)
        result[last] = res
        inc nodeNr
      stmtNr = until
      result.addNodeRange(stm, nodeNr, stmtNr)
      nodeNr = stmtNr
      # echo result.repr
      typNr = -1
  for gen in process :
    # echo gen.repr
    var def = gen.def
    if stmtNr != gen.node : emitNodes(result, s, gen.node)
    if not isNil(def.pre.node) and gwType in gen.gen :   
      if typNr == -1 :
        result.add(newNimNode(nnkTypeSection))
        typNr = 0
      var last = result.len -1
      var res = result[last]
      res.addNodeRange(s[stmtNr], typNr, def.pre.nodeNr)
      result[last] = res
      typNr = def.pre.nodeNr
      var ndClass = getAst(typeDefClassOf(def.cls, def.base))
      # echo result.treeRepr
      ndClass[0][0][tdType][otRecList] = genVMTRecList(def.clsInfo)
      # echo ndClass.treeRepr
      result[last].add(ndClass[0][0])
      ndClass = s[stmtNr][typNr]
      if def.clsInfo.recs.len > 0 :
        echo "recs: ", ndClass.treeRepr 
        #typCls[0][0][tdType][0][otRecList] = def.clsInfo.recs
      result[last].add(ndClass)
      inc typNr
      # echo s[stmtNr][typNr].repr
    elif gwType in gen.gen :
      let ndClass = getAst(typeDefClassOf(def.cls, def.base))
      # echo result.treeRepr
      ndClass[0][0][tdType][otRecList] = genVMTRecList(def.clsInfo)
      result.add(ndClass[0]) 
      # echo result.treeRepr
      let typCls = getAst(typeDefClass(def.cls, def.base))
      # echo typCls.treeRepr
      typCls[0][0][tdType][0][otRecList] = def.clsInfo.recs
      result[result.len-1].add(typCls[0][0])
    if gwImpl in gen.gen :
      result.add getAst(implClassOf(def.cls, def.base))
      # adding forward proc headers first
      result.addForwardProcs(def.clsInfo)          
      # now spit out the virtual procs  
      result.addVirtualStubs(def)        
      # now the implementations of the normal procs
      for i in 0 .. < def.clsInfo.normalProcs.len :
        var p = def.clsInfo.normalProcs[i]
        result.add(p)
      # create the class initialization code
      result.addClassOfInit(def)
      nodeNr = stmtNr + 1
  emitNodes(result, s, s.len)
  when defined(debugOOP) :
    echo result.repr    
  