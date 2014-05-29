#
#                  nimrod-tools
#        (c) Copyright 2013 Adrian Veith
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## This module implements a general purpose forLoop template
## unlike iterators it can advance

import macros
macro lenOfExpr(e) : int =
  #echo lispRepr(e), " ", lispRepr(e[1]), " ", e.len
  #echo e[1].len, " ", lispRepr(e[1])
  return e.len

template forLoop* (x, it: expr, loop: stmt) : stmt {.immediate, dirty.} =
  bind forloops.lenOfExpr
  block:
    var proceed {.noinit.}: bool 
    when lenOfExpr(it) > 0 :
      var iter = it
      var `x` {.inject.} = next(iter, proceed)
      while proceed :
        loop
        `x` = next(iter, proceed)
    else :
      var `x` {.inject.} = next(it, proceed)
      while proceed :
        loop
        `x` = next(it, proceed)
    
proc advance* [T](it: T): bool {.inline.} =
  discard it.next(result)
        
type
  TCounterUp = object
    first, last, step, x: int
  TCounterDown = object 
    first, last, step, x: int

proc countup(a, b: int, step = 1): TCounterUp {.inline.} =
  result.first = a
  result.last = b
  result.step = step
  result.x = a
  
proc next(it: var TCounterUp, proceed: var bool): int {.inline.} =
  result = it.x
  proceed = result <= it.last
  if proceed :
    inc(it.x, it.step)

proc countdown(a, b: int, step = 1): TCounterDown {.inline.} =
  result.first = a
  result.last = b
  result.step = step
  result.x = a
  
proc next(it: var TCounterDown, proceed: var bool): int {.inline.} =
  result = it.x
  proceed = result >= it.last
  if proceed :
    dec(it.x, it.step)

when isMainmodule:

  forloop(i, countup(1,10)):
    echo i

  forloop(i, countdown(20,1)):
    echo i

  import benchmark

  when defined(release) :
    const cLoopMax = 1_000_000_000
  else :
    const cLoopMax = 1_000
  
  var cnt = 0
  bench():
    forloop(i, countup(1, cLoopMax)):
      cnt = cnt + i
  cnt = 0
  bench():
    for i in 1 .. cLoopMax:
      cnt = cnt + i

  for i in countup(1, cLoopMax):
    cnt = cnt + i

  
  
  
  