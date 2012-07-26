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
# Contributors:
#   Adrian Veith
#

## The ``helper`` module implements some hopefully useful routines

import math


proc itrunc* (v: float): int {.inline, noStackFrame.} = 
  {.emit: """ return (int)(v);  """ .}

proc frac* (value: Float): Float {.inline.} =
  return value - trunc(value)


#proc ftrunc* (value: Float): Float {.inline.} =
#  return if value >= 0 : floor(value) else : ceil(value)


const stellen = [0.00000001,0.0000001,0.000001,0.00001,0.0001,0.001,0.01,0.1,
  1.0, 10.0, 100.0, 1000.0, 10000.0, 100000.0, 1000000.0, 10000000.0, 100000000.0]

proc round* (x: Float, n: Int): Float =
  if (n > 8) or (n < -8) :
    return x
  else :
    let sf = stellen[n + 8]
    let xx = x * sf
    return (trunc(xx) + trunc(frac(xx) * 2)) / sf 


proc roundUp* (x: Float, n: Int): Float =
  if (n > 8) or (n < -8) :
    return x
  else :
    let sf = stellen[n + 8]
    var  xx = x * sf
    if frac(xx) > 0 : xx += 1.0
    return trunc(xx) / sf

proc roundDown* (x: Float, n: Int): Float =
  if (n > 8) or (n < -8) :
    return x
  else :
    let sf = stellen[n + 8]
    var xx = x * sf
    return trunc(xx) / sf



when isMainModule:

  echo round(4.125, 2), " ", 4.13, " ", round(4.125, 2) - 4.13
  echo round(PI, 3), " ", 3.141, " ", round(PI, 3) - 3.142
  assert round(PI, 3) == 3.142
  echo round(PI, 4)    
  assert round(PI, 4) == 3.1416

  assert roundDown(PI, 4) == 3.1415

  echo frac(-3.123), " ", -3.0 + frac(-3.123)

  echo 43.9.toInt
  echo 43.9.itrunc
