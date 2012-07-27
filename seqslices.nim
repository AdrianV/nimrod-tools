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
## thanks to the tipps of Araq - code completly changed, using more nimrod features 

type
  TSeqData [T] = array[0 .. 1000_000_000, T]
  TGenSeqInfo {.pure.} [T] = object
    len, space: int
    data: TSeqData [T]
  PGenSeq*[T] = ptr TGenSeqInfo[T]
  PSeqData [T] = ptr TSeqData [T]
  TSeqSlice* {.final, pure, shallow.}[T] = object
    base: PSeqData [T]
    lenX: int
    data: seq[T]
  PSeqSlice* [T] = ref TSeqSlice[T]


when sizeof(int) == 4:
  const seqUniqueFlag = 1 shl 31

when sizeof(int) == 8:
  const  seqUniqueFlag = 1 shl 63

proc len* [T] (me: TSeqSlice[T]): int {.inline.} = 
  # return then len of a TSeqSlice
  return me.lenX and not seqUniqueFlag

proc rebase[T] (me: var TSeqSlice[T], x: int) {.inline.} =
  me.base = cast[PSeqData [T]](addr cast[PGenSeq[T]](me.data).data[x])

proc all* [T] (fseq: seq[T]): TSeqSlice[T] =
  # copy a seq[T] to a TSeqSlice[T]
  result.data= fseq
  result.lenX = result.data.len or seqUniqueFlag
  rebase(result, 0)
  # result.base = cast[PSeqData [T]](addr cast[PGenSeq[T]](result.data).data)

proc all* [T] (fseq: TSeqSlice[T]): TSeqSlice[T] =
  # TSeqSlices are shallow copied
  shallowcopy(result.data, fseq.data)
  result.lenX = result.data.len
  result.base = fseq.base

proc createSeqSlice* [T](newLen: int): TSeqSlice[T] =
  result.len = newLen
  
proc slice* [T] (data: openarray[T], x: TSlice[int]): TSeqSlice[T] =
  # create a slice from an openarray[T]
  let l = data.len
  if x.a < l :
    let l2 = min(l - x.a, x.b - x.a + 1)
    newSeq(result.data, l2)
    for i in 0.. <l2:
      result.data[i] = data[i + x.a]
    result.lenX = l2 or seqUniqueFlag
  else : # empty
    result.data= @[]
    result.lenX = seqUniqueFlag
  rebase(result, 0)

proc all* [T] (data: openarray[T]): TSeqSlice[T] {.inline.} =
  return data.slice(0..data.len)

proc ofs* [T] (me: TSeqSlice[T]): int {.inline.} =
  return (cast[int](me.base) - cast[int](addr cast[PGenSeq[T]](me.data).data)) div sizeof(T)

template sliceImpl() =
  shallowcopy(result.data, fseq.data)
  let l = fseq.len
  if x.a < l :
    result.lenX = min(l - x.a, x.b - x.a + 1)
    rebase(result, x.a + fseq.ofs)
    # result.base = cast[PSeqData [T]](addr cast[PGenSeq[T]](result.data).data[x.a + fseq.ofs])
  else :
    rebase(result, 0)
  
proc slice* [T] (fseq: TSeqSlice[T], x: TSlice[int]): TSeqSlice[T] =
  # create a shallow slice from a slice
  sliceImpl()
      
proc reslice* [T] (me: var TSeqSlice[T], x: TSlice[int]) = 
  let l = me.data.len
  if x.a < l :
    me.lenX = min(l - x.a, x.b - x.a + 1) or (me.lenX and seqUniqueFlag)
    rebase(me, x.a)
  else :
    me.lenX = (me.lenX and seqUniqueFlag)
    rebase(me, 0)
  
proc `[]`* [T] (fseq: TSeqSlice[T], x: TSlice[int]): TSeqSlice[T] {.inline.} =
  # same as slice
  sliceImpl()
  
template checkbounds() = 
  when not defined(release) :
    if x < 0 or x >= me.len : raise newException(EInvalidIndex, "index out of bounds")
  nil

proc `[]`* [T] (me: TSeqSlice[T], x: int) : T {.inline.} =
  # array like access of element x
  checkbounds()
  return me.base[x]
  
iterator items*[T](me: TSeqSlice[T]): T {.inline.} =
  # iterate over all items of a slice
  var base = me.base
  let last = addr base[me.len]
  while base < last:
    yield base[0]
    base = cast[PSeqData [T]](addr base[1])

iterator mitems*[T](me: TSeqSlice[T]): var T {.inline.} =
  # iterate over all items of a slice
  var base = me.base
  let last = addr base[me.len]
  while base < last:
    yield base[0]
    base = cast[PSeqData [T]](addr base[1])

iterator pairs*[T](me: TSeqSlice[T]): tuple[key: int, val: T] {.inline.} =
  # iterate over all (index, item) pairs of a slice
  var i = 0
  var base = me.base
  let last = addr base[me.len]
  while base < last:
    yield (i, base[0])
    base = cast[PSeqData [T]](addr base[1])
    inc(i)

proc makeUnique[T] (me: var TSeqSlice[T]) = 
  let l = me.len
  var temp: seq[T]
  newSeq(temp, l)
  for i in 0.. < l :
    temp[i] = me[i]
  shallowCopy(me.data, temp)
  rebase(me, 0)
  me.lenX = l or seqUniqueFlag

proc `[]=`* [T] (me: var TSeqSlice[T], x: int, val : T) {.inline.} =
  # change element x of the slice. changes are not passed to the parent
  # the slice is unlinked from the parent
  checkbounds()
  if (me.lenX and seqUniqueFlag) == 0: makeUnique(me)
  me.base[x] = val

proc setLen* [T](me: var TSeqSlice[T], newLen: Int) =
  # change the len of a slice
  if me.data != nil :
    var l =  me.data.len
    if newLen > l:
      var temp: seq[T]
      l = l - me.ofs
      newSeq(temp, newLen)
      for i in 0.. < l :
        temp[i] = me.base[i]
      shallowCopy(me.data, temp)
      rebase(me, 0)
      me.lenX = newLen or seqUniqueFlag
    else :
      me.lenX = newLen or (me.lenX and seqUniqueFlag)
  else:
    newSeq(me.data, newLen)
    rebase(me, 0)
    me.lenX = newLen or seqUniqueFlag
    
proc `len=` * [T](me: var TSeqSlice[T], newLen: Int) {.inline.} =
  setLen(me, newLen)

proc newSeqSlice* [T] (me: var PSeqSlice[T], data: openarray[T], x: TSlice[int]) =
  new(me)
  me[] = data.slice(x)

proc newSeqSlice* [T] (me: var PSeqSlice[T], data: openarray[T]) =
  newSeqSlice(me, data, 0 .. data.len)

proc newSeqSlice* [T] (me: var PSeqSlice[T], data: TSeqSlice[T], x: TSlice[int]) =
  new(me)
  me[] = data.slice(x)
  
when isMainModule:

  proc show[T] (arr: T, info: string = "") =
    stdout.write(info)
    var delim = '['
    for el in arr :
      stdout.write(delim)
      stdout.write($el)
      delim = ','
    if delim == '[' : stdout.write(delim)
    echo ']'

  var test = all(@[1,2,3,4,5,6,7,8,9])

  test.show("test: ")

  var p2: PSeqSlice[int]
  newSeqSlice(p2, test, 4..7)
  p2[].show()
  
  var t2= test.all()
  
  t2.show("t2: ")

  test.len = 0
  t2.show("t2: ")
  test.show("test: ")
  test.len = 7
  test.show("test: ") # test and t2 are still using the same array

  test[2] = 314
  t2.show("t2: ")

  t2.len = 19 # now they are unlinked
  t2.show("t2: ")
  test.show("test: ")
  test[2] = 66
  test.show("test: ")
  t2.show("t2: ")
  
  var t3 = [1,2,3,4,5,6,7,8,9].slice(1..100)

  t3.show("t3: ")

  var t4 = t3.slice(2..6)

  t4.show("t4: ")

  t3[2] = 99

  t3.show("t3: ")
  t4.show("t4: ")
  
  proc getTest(): TSeqSlice[int] =
    return @[1,2,3,4,5,6,7,8,9].slice(1..5)

  t4 = getTest()
  t4.show("t4: ")
  t3.show("t3: ")    

  proc oldTest() =
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
    # test = nil
    # t2 = nil
    GC_fullCollect()
    stest.show("still alive: ")
    t3.show("me too: ")

  oldTest()

  t4 = t3.slice(99..1000)
  t4.show()
  t3 = t4.slice(0..5)
  t3.show()
  t3.reslice(0..5)
  t3.show()

  