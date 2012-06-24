#
#                                                                                                  
# The contents of this file are subject to the Mozilla Public License Version 1.1 (the "License"); 
# you may not use this file except in compliance with the License. You may obtain a copy of the    
# License at http://www.mozilla.org/MPL/                                                           
#                                                                                                  
# Software distributed under the License is distributed on an "AS IS" basis, WITHOUT WARRANTY OF   
# ANY KIND, either express or implied. See the License for the specific language governing rights  
# and limitations under the License.                                                               
#
# (c) Copyright 2012 Adrian Veith
#

## The ``seqslices`` module implements D like array slices for Nimrod. The idea is, 
## that a slice of an array doesn't copy the values of an array. Instead a slice only 
## keeps a reference to its parent slice and an offset. If the underlying slice is changed,
## the changes are reflected by its childs as long as possible. Otherwise the child slices
## are unlinked from its parent
##
## the current implementation is merly a proof of concept and uncomplete. Bugs expected !


type
  PtrSeqSlice [T] = ptr TSeqSlice[T]
  PSeqSlice* [T] = ref TSeqSlice[T]
  TSliceableSeq {.final, pure.}[T] = object
    arr: seq[T]
    head, tail: PtrSeqSlice[T]
  TSeqSlice* {.final, pure.}[T] = object
    base: ptr T
    next, prev: PtrSeqSlice[T]
    arr: ptr TSliceableSeq[T]
    ofs: int32
    len: int32
    own: ref TSliceableSeq[T]
  


proc finalize[T] (me: ref TSliceableSeq[T]) 
proc remove[T] (me: PSeqSlice[T]) 

proc initSliceableSeq[T](me: ref TSliceableSeq[T], len: int) {.inline.} =
  newSeq(me.arr, len)
    
proc newSliceableSeq [T] (me: var ref TSliceableSeq[T], len: int) =
  new(me, finalize[T])
  initSliceableSeq(me, len)  

proc setBounds[T](me: PSeqSlice[T], arr: var seq[T], a, b: int) {.inline.} = 
  let l = arr.len
  if a < l :
    me.ofs = a
    me.len = min(l - a, b - a + 1)
    me.base = addr arr[a]
  
proc all* [T] (fseq: seq[T]): PSeqSlice[T] =
  # make a slice from an existing seq. The seq is copied
  new(result, remove[T])
  new(result.own, finalize[T])
  result.own.arr = fseq
  setBounds(result, result.own.arr, 0, fseq.len)

proc slice* [T] (fseq: seq[T], x: TSlice[int]): PSeqSlice[T] =
  # make a slice from an existing seq with bounds. The seq is copied
  new(result, remove[T])
  new(result.own, finalize[T])
  result.own.arr = fseq
  setBounds(result, x.a, x.b)

proc newSeqSlice* [T](me: var PSeqSlice[T], newLen: int) =
  # create a new slicable slice
  new(result, remove[T])
  new(result.own, finalize[T])
  newSeq(result.own.arr, newLen)
  setBounds(result, 0, newLen)


proc append[T] (me: var TSliceableSeq[T], arr: ptr TSeqSlice[T]) {.inline.} =
  arr.arr = addr me
  arr.next = me.head
  me.head = arr
  if me.tail == nil :
    me.tail = me.head
  else:
    arr.next.prev = arr

proc initSeqSlice[T] (me: var TSeqSlice[T], parent: var TSliceableSeq[T]) {.inline.} =
  me.arr = addr parent
  append(parent, addr me)

proc newFrom [T](me: var PSeqSlice[T], parent: var TSliceableSeq[T]) {.inline.} =
  new(me, remove[T]) 
  initSeqSlice(me[], parent)
  
proc slice* [T] (me: PSeqSlice[T], x:TSlice[int]): PSeqSlice[T] =
  # slice a slicable slice. no data is copied here
  if me.arr != nil :
    # inherit parent slice
    newFrom(result, me.arr[])
    setBounds(result, me.arr.arr, x.a + me.ofs, x.b + me.ofs)
  else :
    # me is parent 
    newFrom(result, me.own[])
    setBounds(result, me.own.arr, x.a, x.b)

proc `[]`* [T] (me: PSeqSlice[T], x:TSlice[int]): PSeqSlice[T] {.inline.} =
  # same as slice for conviniance
  return me.slice(x)

template checkbounds() = 
  when not defined(release) :
    if x < 0 or x >= me.len : raise newException(EInvalidIndex, "index out of bounds")
  nil

proc getX [T] (me: var TSeqSlice[T], x: int) : T {.inline.} =
  checkbounds()
  return cast[ptr T](cast[int](me.base) + x * sizeof(T)) []

proc `[]`* [T] (me: PSeqSlice[T], x: int) : T {.inline.} =
  # array like access of element x
  checkbounds()
  return cast[ptr T](cast[int](me[].base) + x * sizeof(T)) []
  
iterator items*[T](me: PSeqSlice[T]): T {.inline.} =
  # iterate over all items of a slice
  var i = 0
  while i < me.len:
    yield me[i]
    inc(i)

iterator pairs*[T](me: PSeqSlice[T]): tuple[key: int, val: T] {.inline.} =
  # iterate over all (index, item) pairs of a slice
  var i = 0
  while i < me.len:
    yield (i, me[i])
    inc(i)


template unbindImpl =    
  var me = arr.arr
  if arr.prev == nil : # me.head == arr 
    me.head = arr.next
    if me.head == nil: me.tail = nil
    else: arr.next.prev = nil
  else: 
    arr.prev.next = arr.next # arr.prev != nil
    if arr.next != nil:
      arr.next.prev = arr.prev
    else: me.tail = arr.prev
  arr.arr = nil
  # echo cast[int](me.head), " ", cast[int](me.tail)
  
proc unbind[T] (arr: var TSeqSlice[T]) {.inline.} =
  unbindImpl

proc unbind[T] (arr: ref TSeqSlice[T]) {.inline.} =
  unbindImpl
  
proc remove[T] (me: PSeqSlice[T]) =
  # echo "remove"
  if me.arr != nil:
    unbind(me)
    
proc makeUnique[T] (me: var TSeqSlice[T]) = 
  # echo "makeUnique"
  if me.arr != nil :
    newSliceableSeq(me.own, me.len)
    # newSeq(me.own, me.len)
    for i in 0.. < me.len :
      me.own.arr[i] = getX(me, i)
    me.base = addr me.own.arr[0]
    unbind(me)

proc `[]=`* [T] (me: PSeqSlice[T], x: int, val : T) {.inline.} =
  # change element x of the slice. changes are not passed to the parent
  # the slice is unlinked from the parent
  checkbounds()
  if me.arr != nil : makeUnique(me[])
  cast[ptr T](cast[int](me[].base) + x * sizeof(T)) [] = val
    
proc rebase[T] (me: var TSliceableSeq[T], x: PSeqSlice[T]) {.inline.} = 
  x.base = cast[ptr T](cast[int](addr me.arr[0]) + x.ofs * sizeof(T))

proc beforeSetLen[T] (me: var TSliceableSeq[T], newLen: int) = 
  # echo "before SetLen"
  var x = me.head
  while x != nil :
    if x.ofs + x.len > newLen:
      makeUnique(x[])
    x = x.next
  
proc rebase[T] (me: var TSliceableSeq[T]) = 
  # echo "rebase"
  var x = me.head
  let l = me.arr.len
  let base = if l > 0 : cast[int](addr me.arr[0]) else : 0
  while x != nil :
    if x.ofs + x.len <= l:
      x.base = cast[ptr T](base + x.ofs * sizeof(T))
    else:
      makeUnique(x[])
    x = x.next
    
proc setLen[T](me: var TSliceableSeq[T], newlen: int) =
  # change the len of a parent. if a child is longer than the
  # newLen, it is unlinked
  beforeSetLen(me, newLen)
  let old = (if me.arr.len != 0 : addr (me.arr[0]) else : nil)
  setLen(me.arr, newLen)
  if newLen != 0 or old != addr me.arr[0] : rebase(me)

proc setLen* [T] (me : PSeqSlice[T], newLen: Int) {.inline.} =
  if me.arr != nil : setLen(me.arr[], newLen)
  else : 
    setLen(me.own[], newLen)
    me.len = newLen

proc finalize[T] (me: ref TSliceableSeq[T]) =
  # echo "finalize"
  when true:
    var x = me.head
    while x != nil :
      makeUnique(x[])
      x = x.next
    
when isMainModule:

  proc show[T] (arr: T, info: string = "") =
    stdout.write(info)
    var delim = '['
    for el in arr :
      stdout.write(delim)
      stdout.write($el)
      delim = ','
    echo ']'

  var test = @[1,2,3,4,5,6,7,8,9].all()

  test.show("initial: ")

  var stest = test.slice(2..4)
  stest.show("[2..4]: ")
  var t2 = test[1..6]
  t2.show("[1..6]: ")
  var t3 = t2[0..1000]
  t3.show("[0..1000] cut of:")
  test[3] = 12
  test.show("test[3] == 12: ")
  stest.show("stest[1] == 12 now: ")
  stest[1] = 5
  stest.show("stest[1] changed: ")
  t2.show("change is not seen by others: ")
  test.show("dito: ")
  test.setLen(7)
  test.show("len changed: ")
  t3.show("untouched: ")
  test = nil
  t2 = nil
  GC_fullCollect()
  stest.show("still alive: ")
  t3.show("me too: ")
