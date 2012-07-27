import times, strutils

template bench* (call: stmt): stmt =
    bind strutils.formatFloat, ffDecimal
    bind times.cpuTime
    block:
        var tStart: Float = cpuTime()
        call
        tStart = cpuTime() - tStart
        if tStart > 10.0 :
          echo strutils.formatFloat(tStart, ffDecimal), " sec"
        else :
          echo toInt(1000.0 * tStart), " ms"

template benchmsg* (msg: expr, call: stmt): stmt =
  stdout.write msg
  bench():
    call