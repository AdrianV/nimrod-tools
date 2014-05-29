#
#                  nimrod-tools
#        (c) Copyright 2013 Adrian Veith
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## This module implements a fast and low level lazy btree

import binsearch,
  strutils,
  traits


type
  PBtree* [T,D] = ref TBTree[T,D]
  TItem* {.acyclic, pure, final, shallow.} [T,D] = object
        key* : T
        value* : D
        node: PBtree[T,D]
        when not isNilable(D) :
          val_set: Bool
  TItems[T,D] = seq[ref TItem[T,D]]
  TBTree* {.acyclic, pure, final, shallow.} [T,D] = object
        slots*: TItems[T,D]
        left*: PBtree[T,D]
        count*: Int32
          
  
  RPath[T,D] = tuple[
    Xi: Int,
    Nd: PBtree[T,D] ]

  TTreeIterator* [T,D] = ref RTreeIterator[T,D]
  RTreeIterator* {.shallow.} [T,D] = object {.inheritable.}
    path: array[0..30, RPath[T,D]]
    level: int
    current: ref TItem[T,D]
    
  PBtreeValueProp* [T,D] = distinct PBtree [T,D]
  

const
  cLen1 = 2
  cLen2 = 16
  cLen3 = 32
  cLenCenter = 80
  clen4 = 96
  cLenMax = 128
  cCenter = cLenMax div 2

proc len* [T,D] (n:PBtree[T,D]): Int {.inline.} =
  return n.Count
  
proc clean[T: TOrdinal|TNumber](o: var T) {.inline.} = nil

proc clean[T: string|seq](o: var T) {.inline.} =
  o = nil

proc clean[T,D] (o: ref TItem[T,D]) {.inline.} = 
  # o.Node = nil
  when isNilable(D) :
    o.Value = nil
  else :
    o.val_set = false

proc isClean* [T,D] (it: ref TItem[T,D]): Bool {.inline.} = 
  when isNilable(D) :
    return it.Value == nil
  else :
    return not it.val_set

proc isClean* [T,D] (n: PBtree[T,D], x: Int): Bool {.inline.} = 
  when isNilable(D) :
    return n.slots[x].Value == nil
  else :
    return not n.slots[x].val_set
    
proc setItem[T,D] (AKey: T, AValue: D, ANode: PBtree[T,D]): ref TItem[T,D] {.inline.} = 
  new(Result)
  Result.Key = AKey
  Result.Value = AValue
  Result.Node = ANode
  when not isNilable(D) :
    Result.val_set = true

proc setItem[T,D] (AKey: T, ANode: PBtree[T,D]): ref TItem[T,D] {.inline.} = 
  new(Result)
  Result.Key = AKey
  Result.Node = ANode
  when not isNilable(D) :
    Result.val_set = true

proc cmpInline * (a, b: string): int {.inline.} =
  var x = 0
  while true :
    result = ord(a[x]) - ord(b[x])
    if result != 0 or a[x] == '\0' : break    
    inc(x)   
    result = ord(a[x]) - ord(b[x])
    if result != 0 or a[x] == '\0' : break    
    inc(x)   

when false:
  proc bSearch [T,D] (haystack: PBtree[T,D], needle:T): Int {.inline.} =
    when T is int:
      template compare(I): int = haystack.slots[I].key - needle
    elif T is string :
      template compare(I): int = haystack.slots[I].key.cmpInline(needle)
    else :
      template compare(I): int = haystack.slots[I].key.cmp(needle)
    binSearchImpl(haystack.count.int, result, compare )

else :
          
  # echo "a == at ", scmp("a", "at")       
  proc bSearch [T,D] (haystack: PBtree[T,D], needle:T): Int {.inline.} =
    # bind binSearchImplLitStrict
    # bind binSearchImpl
    when T is int:
      template less(I: expr): bool = haystack.slots[I].key < needle 
      template equal(I: expr): bool = haystack.slots[I].key == needle 
    elif compiles(cmpInline(needle, needle)) :
      var SW: Int 
      template less(I: expr): bool =
        SW = cmpInline(haystack.slots[I].key, needle)
        SW < 0
      template equal(I: expr): bool = 
        SW == 0 
    else :
      var SW: Int
      template less(I: expr): bool = 
        SW = haystack.slots[I].key.cmp(needle)
        SW < 0 
      template equal(I: expr): bool = 
        SW == 0 
    binSearchStrictImpl(haystack.count.int, less, equal, result)

proc arrDel[T:int|ptr|ref] (arr: var seq[T], x, cnt: int) {.inline.} =
  var delta = cnt - 1 - x
  if x >= 0 :
    if delta > 0 :
      moveMem(addr arr[x], addr arr[x + 1], sizeof(T) * delta)
    cast[ptr int](addr arr[cnt - 1])[] = 0
    
proc arrIns[T:int|ptr|ref] (arr: var seq[T], x, cnt: int) {.inline.} =
  var delta = cnt - x
  if x >= 0 :
    if delta > 0 :
      moveMem(addr arr[x+1], addr arr[x], sizeof(T) * delta)
    cast[ptr int](addr arr[x])[] = 0

proc arrCopyClear[T:int|ptr|ref] (dest, source: var seq[T], startDest, startSource, cnt: int) {.inline.} =
  if cnt > 0 :
    copyMem(addr dest[startDest], addr source[startSource], cnt * sizeof(T))
    zeroMem(addr source[startSource], cnt * sizeof(T))

proc DeleteItem[T,D] (n: PBtree[T,D], x: Int): PBtree[T,D] {.inline.} =
  var w = n.slots[x]
  if w.Node != nil : 
    clean(w)
    return n
  # CleanKey(w.Key);  
  if n.Count > 1 :
    n.slots[x] = nil
    arrDel(n.slots, x, n.Count)
    dec(n.Count)
    
    #for i in countup(x, n.Count -1) : shallowCopy(n.slots[i], n.slots[i + 1])
    #n.slots[n.Count] = nil
    
    case n.Count 
    of cLen1 : setLen(n.slots, cLen1)
    of cLen2 : setLen(n.slots, cLen2)
    of cLen3 : setLen(n.slots, cLen3)
    of cLenCenter : setLen(n.slots, cLenCenter)
    of cLen4 : setLen(n.slots, cLen4)
    else: discard
    Result = n
    
  else :
    Result = n.Left
    n.slots = nil
    n.Left = nil
  
template findImpl[T,D] (node: PBtree[T,D], key: expr, onFound: expr, onPath: expr): stmt {.immediate.} =
  while node != nil :
    var x = bSearch(node, key)
    if x <= 0 :
      onPath(node, x)
      if x == 0 :
        node = node.Left
      else :
        x = (-x) -1
        if x < node.Count : 
          node = node.slots[x].Node
        else :
          break
    else :
      dec(x)
      onFound(node, x)

#template deleteImpl(T,D: typedesc, node: expr, key: expr, onResult: expr, onNewRoot: expr): stmt {.immediate.} =

template doDelPath(n: expr, x: expr) {.immediate.} =
  Path[h].Nd = n
  Path[h].Xi = -x
  inc(h)
  
template doDelFound(n: expr, x: expr) {.immediate.} =  
  if isClean(n, x) : return
  doResult(n.slots[x])
  # AValue = n.slots[x].Value
  var n2 = DeleteItem(n, x)
  dec(h)
  while (n2 != n) and (h >=0) :
    n = n2 
    var w = addr Path[h]
    x  = w.Xi -1
    if x >= 0 :
      if (n == nil) and isClean(w.Nd, x) :
        n = w.Nd
        n.slots[x].Node = nil 
        n2 = DeleteItem(n, x)
      else :
        w.Nd.slots[x].Node = n
        return
    else :
      w.Nd.Left = n
      return
    dec(h)
  if h < 0:
    ANode = n2 # Result = n2
  return
  
proc DeleteSlot* [T,D] (ANode: var PBtree[T,D], key: T): ref TItem[T,D] =
  var Path: array[0..30, RPath[T,D]]
  var h = 0
  var node = ANode
  template doResult(res: expr) {.immediate.} =
    Result = res 
  findImpl (node, key, doDelFound, doDelPath)

proc Delete* [T,D] (ANode: var PBtree[T,D], key: T) =
  var Path: array[0..30, RPath[T,D]]
  var h = 0
  var node = ANode
  template doResult(res: expr) {.immediate.} = discard
  findImpl (node, key, doDelFound, doDelPath)
  # if not isNil(it) : result = it.value
  
proc find* [T,D] (n: PBtree[T,D], key: T): ref TItem[T,D] =
  template doPath(n, x: expr) {.immediate.} = discard
  template doFound(n, x: expr) {.immediate.} = 
    return n.slots[x]
  var node = n
  findImpl(node, key, doFound, doPath)

var line: string = ""
proc swrite (data: varargs[string]) =
  for s in items(data) : 
    line = line & s

proc swriteln (data: varargs[string]) =
  swrite data
  echo line
  line = ""
     
proc traceTree* [T,D](root: PBtree[T,D]) =

    
  proc traceX(x: Int) = 
    swrite "(", $x, ") "
    
  proc traceEl(el: ref TItem[T,D]) =
    swrite " key: ", $el.Key, " value: ", $el.Value
    
  proc traceln(space: string) =
    swriteln() 
    swrite space
    
  proc doTrace(n: PBtree[T,D], level: Int) =
    var space = repeatChar(2 * level)
    traceln(space)
    swrite "node: "
    if n == nil:
      swriteln "is empty"
      return
    swrite ($n.Count, " elements: ")
    if n.Left != nil:
      traceln(space)
      swrite "left: "
      doTrace(n.left, level +1)
    for i, el in n.slots :
      if el != nil and not isClean(el):
        traceln(space)
        traceX(i)
        if i >= n.Count: 
          swrite "error "
        else:
          traceEl(el)
          if el.Node != nil: doTrace(el.Node, level +1)
          else : swrite " empty "
      elif i < n.Count :
        traceln(space)
        traceX(i)
        swrite "clean: "
        when isNilable(T) :
          if el.Key != nil: swrite el.Key
        else : swrite $el.Key
        if el.Node != nil: doTrace(el.Node, level +1)
        else : swrite " empty "
    swriteln ()
    
  doTrace(root, 0)
  
proc findOrInsert* [T,D](ANode: var PBTree[T,D], AKey: T): ref TItem[T,D] = 
  var Path: array[0..30, RPath[T,D]]
  var h = 0
  template doPath(n, x: expr) {.immediate.} =
    Path[h].Nd = n
    Path[h].Xi = -x
    inc(h)
  template doFound(n, x: expr) {.immediate.} = 
    return n.slots[x]
  template setSlot(slot, item, node: expr) {.immediate.} =
    if isNil(item): 
      result = setItem(AKey, node)
      slot = result 
    else :      
      item.node = node
      slot = item
  template InsertItem (APath: RPath[T,D], ANode:PBtree[T,D], AItem: ref TITem[T,D]) {.immediate.} =
    var x = APath.Xi
    inc(APath.Nd.Count)
    case APath.Nd.Count 
    of cLen1: setLen(APath.Nd.slots, cLen2)
    of cLen2: setLen(APath.Nd.slots, cLen3)
    of cLen3: setLen(APath.Nd.slots, cLenCenter)
    of cLenCenter: setLen(APath.Nd.slots, cLen4)
    of cLen4: setLen(APath.Nd.slots, cLenMax)
    else: discard
    arrIns(APath.Nd.slots, x, APath.Nd.Count.int - 1)
    setSlot(APath.Nd.slots[x], AItem, ANode)
  template SplitPage (n, left: PBtree[T,D], xi: Int, AItem: ref TITem[T,D]) {.immediate.} =
    var x = Xi
    var node: PBtree[T,D]
    new(node)
    node.slots.newSeq(cLenCenter)
    node.Count = cCenter
    if x == cCenter:
      arrCopyClear(node.slots, left.slots, 0, cCenter, cCenter)
      node.Left = n
    else :
      if x < cCenter :
        arrCopyClear(node.slots, left.slots, 0, cCenter, cCenter)
        arrIns(left.slots, x, cCenter)
        setSlot(left.slots[x], AItem, n)
        AItem = left.slots[cCenter]
        node.Left = AItem.Node
        left.slots[cCenter] = nil
      else :
        x = x - (cCenter + 1)
        arrCopyClear(node.slots, left.slots, 0, cCenter + 1, x)
        setSlot(node.slots[x], AItem, n)
        arrCopyClear(node.slots, left.slots, x + 1, cCenter + 1 + x, cCenter - x -1)
        AItem = left.slots[cCenter]
        node.Left = AItem.Node
        left.slots[cCenter] = nil
    left.Count = cCenter
    n = node
  
  var node = ANode
  findImpl(node, Akey, doFound, doPath)
  dec(h)
  var left: PBtree[T,D]
  var lItem : ref TITem[T,D]
  while h >= 0 :
    if Path[h].Nd.Count < cLenMax :
      InsertItem(Path[h], node, lItem)
      return
    else :
      left = Path[h].Nd
      SplitPage(node, left, Path[h].Xi, lItem)
    dec(h)
    
  new(ANode)
  ANode.slots.newSeq(cLen1)
  ANode.Count = 1
  ANode.Left = left
  setSlot(ANode.slots[0], lItem, node)
  #ANode.slots[0] = setItem(lKey, lValue, n)
  
  
proc `[]` * [T,D] (n: PBtree[T,D], key: T): D {.inline.} = 
  let it = n.find(key)
  if it != nil : return it.value
  
proc `[]=` * [T,D] (n: var PBtree[T,D], key: T, val: D) {.inline.} = 
  n.findOrInsert(key).value = val


proc CleanTree* [T,D](n: var PBtree[T,D]) =
  if n.Left != nil :
    CleanTree(n.Left)
  for i in 0 .. n.Count - 1 :
    if n.slots[i].Node != nil :
        CleanTree(n.slots[i].Node)
    n.slots[i] = nil
    #clean(w.Value)
    #clean(w.Key)
  n.slots = nil
  n = nil


proc VisitAllNodes* [T,D](n: PBtree[T,D], visit: proc(n: PBtree[T,D]): PBtree[T,D] {.closure.} ): PBtree[T,D] =
  if n != nil :
    if n.Left != nil :
      n.Left = VisitAllNodes(n.Left, visit)    
    for i in 0 .. n.Count - 1 :
      var w = n.slots[i]
      if w.Node != nil :
        w.Node = VisitAllNodes(w.Node, visit)    
    return visit(n)
  return nil

proc VisitAllNodes* [T,D](n: PBtree[T,D], visit: proc(n: PBtree[T,D]) {.closure.} ) =
  if n != nil:
    if n.Left != nil :
      VisitAllNodes(n.Left, visit)    
    for i in 0 .. n.Count - 1 :
      var w = n.slots[i]
      if w.Node != nil :
        VisitAllNodes(w.Node, visit)    
    visit(n)

template VisitAllImpl(doVisitNode, doVisit: expr, testForDelete: Bool) {.immediate.} =
  if n != nil:
    var n1 = n.Left
    if n1 != nil :
      when testForDelete : 
        var n2 = doVisitNode(n1)
        if n1 != n2 :
          n.Left = n2
      else: doVisitNode(n1)
    var i = 0
    while i < n.Count :
      var w = n.slots[i]
      if not w.isClean :
        when testForDelete :
          if doVisit(w) :
            Result = DeleteItem(n, i)
            if Result == nil : return
            dec(i)
        else: doVisit(w)
      n1 = w.Node
      if n1 != nil :
        when testForDelete :
          var n2 = doVisitNode(n1)
          if n1 != n2 :
            w.Node = n2
        else:doVisitNode(n1)
      inc(i)

when false:
  iterator allKeys* [T,D](n: PBtree[T,D]): T {.closure.} =
    template doVisitNode(n: expr) =
      for x in allKeys(n) :
        yield x
    template doVisit(w: expr) =
      yield w.Key
    VisitAllImpl(doVisitNode, doVisit, false)

proc forEach* [T,D](n: PBtree[T,D], visit: proc(AKey: T, AValue: D) {.closure.} ) =
  template doVisitNode(n: expr) =
    forEach(n, visit)
  template doVisit(w: expr) =
    visit(w.Key, w.Value) 
  VisitAllImpl(doVisitNode, doVisit, false)

proc forEachDelete* [T,D](n: PBtree[T,D], visit: proc(AKey: T, AValue: var D):Bool {.closure.} ): PBtree[T,D] =
  template doVisitNode(n: expr): PBtree[T,D] =
    forEachDelete(n, visit)
  template doVisit(w: expr): Bool =
    visit(w.Key, w.Value) 
  VisitAllImpl(doVisitNode, doVisit, true)
  return n

proc forEach* [T,D](n: PBtree[T,D], visit: proc(AKey: T, AValue: var D) {.closure.} ) =
  template doVisitNode(n: expr) =
    forEach(n, visit)
  template doVisit(w: expr) =
    visit(w.Key, w.Value) 
  VisitAllImpl(doVisitNode, doVisit, false)

proc forEachKey* [T,D](n: PBtree[T,D], visit: proc(AKey: T) {.closure.} ) =
  template doVisitNode(n: expr) =
    forEachKey(n, visit)
  template doVisit(w: expr) =
    visit(w.Key) 
  VisitAllImpl(doVisitNode, doVisit, false)

proc initIterator [T,D] (it: TTreeIterator[T,D], n: PBtree[T,D]) {.inline.} = 
  it.Path[0].Nd = n
  it.Path[0].Xi = -1

proc getNext[T,D] (it: TTreeIterator[T,D]): ref TItem[T,D] =
  var level = it.level
  var nd = it.Path[level].Nd
  if nd != nil :
    var i = it.Path[level].Xi
    while true : 
      if i < nd.Count :
        it.Path[level].Nd = nd
        it.Path[level].Xi = i
        if i < 0 :
          if nd.Left != nil :
            nd = nd.Left
            inc(level)
          else : inc(i)
        else :
          var w = nd.slots[i]
          if not w.isClean() :
            it.level = level
            if w.Node != nil :
              inc(level)
              it.Path[level].Xi = -1
              it.Path[level].Nd = w.Node
              it.level = level
            else :
              it.Path[level].Xi = i + 1
            return w
          if w.Node != nil :
            nd = w.Node
            i = -1
            inc(level)
          else : inc(i)
      else :
        dec(level)
        if level < 0 : break
        nd = it.Path[level].Nd
        i = it.Path[level].Xi
        inc(i)
  return nil

template defineIterator(name: expr) {.immediate, dirty.} =
  type
    `TIterator name`* [T,D] = ref `RIterator name` [T,D]
    `RIterator name`* [T,D] = object of RTreeIterator[T,D]
  
  proc `name`* [T,D](n: PBtree[T,D]): `TIterator name`[T,D] = 
    new(result)
    initIterator(cast[TTreeIterator[T,D]](result), n)

defineIterator(Keys)

proc next* [T,D](it: TIteratorKeys[T,D], proceed: var bool): T {.inline.} = 
  let cur = getNext(cast[TTreeIterator[T,D]](it))
  proceed =  cur != nil
  if proceed : return cur.Key  


defineIterator(Values)

proc next* [T,D](it: TIteratorValues[T,D], proceed: var bool): D {.inline.} = 
  let cur = getNext(cast[TTreeIterator[T,D]](it))
  proceed =  cur != nil
  if proceed : return cur.Value


defineIterator(Pairs)

proc next* [T,D](it: TIteratorPairs[T,D], proceed: var bool): tuple[key:T, val:D] {.inline.} = 
  let cur = getNext(cast[TTreeIterator[T,D]](it))
  proceed =  cur != nil
  if proceed : 
    return (cur.key, cur.value)
  
when false:  
  template iteratorImpl(n, yieldImpl: expr) {.immediate.} =
    if n != nil :
      var Path: array[0..20, RPath[T,D]]
      var level = 0
      var nd = n
      var i = -1
      while true : 
        if i < nd.Count :
          Path[level].Nd = nd
          Path[level].Xi = i
          if i < 0 :
            if nd.Left != nil :
              nd = nd.Left
              inc(level)
            else : inc(i)
          else :
            var w = nd.slots[i]
            if not w.isClean() :
              yieldImpl(w)
            if w.Node != nil :
              nd = w.Node
              i = -1
              inc(level)
            else : inc(i)
        else :
          dec(level)
          if level < 0 : break
          nd = Path[level].Nd
          i = Path[level].Xi
          inc(i)
          
  iterator keys* [T,D] (n: PBtree[T,D]): T {.closure.} =
    template yieldImpl(w: expr) = 
      yield w.Key
    iteratorImpl(n, yieldImpl)
else :
  import forLoops

  iterator keys* [T,D] (n: PBtree[T,D]): T {.inline.} =
    forLoop e, keys(n) : yield e

  iterator values* [T,D] (n: PBtree[T,D]): D {.inline.} =
    forLoop e, values(n) : yield e

  iterator pairs* [T,D] (n: PBtree[T,D]): tuple[key:T, val:D] {.inline.} =
    forLoop e, pairs(n) : yield e
      
when isMainModule:

  import times
  import tables
  import benchmark
    
  proc Test(n: PBtree[string, int], Key: string): Int =
    return bSearch[string,int](n, key)
    
  #GC_disable()

  proc TestStringInt() =
    echo "TestStringInt"
    var root: PBtree[string, int]
    findOrInsert[string, int](root, "test").value = 312
    var keep_root = root
    traceTree(root)
    when true:
      echo bSearch(root, "test")
      echo Test(root, "test")
      var it1 = root.Find("test")
      echo "found: ",it1.Value
      var oldKey: Int = 0
      #root = InternalDelete(root, "test", oldKey)
      #echo "oldKey: " , oldKey
      it1 = root.Find("test")
      echo it1 == nil
      traceTree(root)
    when true:
      root["test"] = 1
      traceTree(root)
      it1 = root.Find("test")
      echo it1.Value
      #for k in root.Keys :
      #  echo k
      bench():
        for i in 1..1_000_000:
          #echo i
          root[$i] = i
        
      #traceTree(root)
      bench():      
        for i in 1..1_000_000:
          it1 = root.Find($i)
          if not isNil(it1): discard   #echo it1.Value
          else: echo "not found ", i
      root.Delete("test")
    var cnt = 0
    bench():
      forEach(root, proc(key: string, val: int) = inc(cnt))
    echo cnt
    cnt = 0
    bench():
      forEachKey(root, proc(key: string) = inc(cnt))
    echo cnt
      
  proc TestIntInt() =
    echo "TestIntInt"
    var root: PBTree[int, int]
    root[312] = 312
    var it1 = root.Find(312)
    echo it1.Value
    bench():
      for i in 1..1_000_000:
        root[i] = i
      
    bench():      
      for i in 1..1000_000:
        it1 = root.Find(i)
        if not isNil(it1): discard  #echo it1.Value
        else: echo "not found ", i

    var cnt = 0
    bench():
      forEach(root, proc(key: int, val: int) = inc(cnt))
    echo cnt
    cnt = 0
    forEach(root, proc(key: int, val: int) = inc(cnt))
    echo cnt
    cnt = 0
    bench():
      forLoop e, keys(root) :
        inc(cnt)
    echo cnt
    cnt = 0
    bench():
      forLoop e, values(root) :
        inc(cnt, e)
    echo cnt
    cnt = 0
    bench():
      var iter = keys(root)
      for i in 1 .. 100: discard advance(iter)
      forLoop e, iter :
        inc(cnt)
    echo "a ", cnt
    cnt = 0
    bench():
      for e in root.keys :
        inc(cnt)
    echo "b ", cnt
    
  TestStringInt()    
  TestIntInt()

