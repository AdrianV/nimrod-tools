#
#                  nimrod-tools
#        (c) Copyright 2013 Adrian Veith
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## This module implements compile time macro helper procedures

import macros

macro dump* (): stmt  {.immediate.} =
  let n = callsite()
  echo n.lisprepr
  
proc append* (father, child: PNimrodNode): PNimrodNode  {.compiletime.} =
  father.add(child)
  return father

proc append* (father: PNimrodNode, children: varargs[PNimrodNode]): PNimrodNode  {.compiletime.} =
  father.add(children)
  return father

proc insert* (father: PNimrodNode, indx: int, children: varargs[PNimrodNode]): PNimrodNode  {.compiletime.} =
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
