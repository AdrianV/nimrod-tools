#
#                  nimrod-tools
#        (c) Copyright 2013 Adrian Veith
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## This module implements a simple benchmark template

import strutils

when not defined(JS) :
  import times

  proc timeStampInMS * () : float {.inline.} = cpuTime() * 1000.0
  
  proc formatTime(val: float, prec: int): string {.inline.} = val.formatFloat(ffDecimal, prec)

else :
  type
    TDate {.final, importc.} = object
      getTime: proc (): float
  proc newDate() : TDate {.importc: "new Date", nodecl.}
  
  proc timeStampInMS * () : float {.inline.} = newDate().getTime()

  template formatTime(val: float, prec: int): string = 
    $val
  

template bench* (call: stmt): stmt =
    bind timeStampInMS, formatTime
    block:
        let tStart = timeStampInMS()
        call
        let dur = timeStampInMS() - tStart
        if dur > 9999.9 :
          echo formatTime(dur / 1000.0, 2), " s"
        else :
          echo formatTime(dur, 1), " ms"

template bench* (msg: expr, call: stmt): stmt =
  stdout.write msg & ": "
  bench():
    call