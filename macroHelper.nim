#
#                  nimrod-tools
#        (c) Copyright 2013 Adrian Veith
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## This module implements compile time macro helper procedures

import macros

const
  pdIdent* = 0
  pdFormalParams* = 3
  pdPragma* = 4
  pdBody* = 6
  tdType* = 2
  otRecList* = 2
  doStmtList* = 6
  
macro dump* (): stmt  {.immediate.} =
  let n = callsite()
  echo n.lisprepr

when false:  
  proc append* (father, child: PNimrodNode): PNimrodNode  {.compiletime.} =
    father.add(child)
    return father

  proc append* (father: PNimrodNode, children: varargs[PNimrodNode]): PNimrodNode  {.compiletime.} =
    father.add(children)
    return father

proc insert* (father: PNimrodNode, indx: int, children: varargs[PNimrodNode]): PNimrodNode  {.compiletime.} =
  var indx = Min(indx, father.len)
  result = newNimNode(father.kind)
  for i in 0 .. < indx :
    result.add(father[i])
  result.add(children)
  for i in indx .. < father.len :
    result.add(father[i])

proc paramsRange* (pdNode: PNimrodNode, fromIndx: Int, toIndx: Int): seq[PNimrodNode] {.compiletime.} =
  result = @[]
  var params = pdNode[pdFormalParams]
  for i in fromIndx .. < params.len :
    if toIndx >= 0 and i > toIndx : break
    result.add(params[i])

proc paramsIdentRange* (pdNode: PNimrodNode, fromIndx: Int, toIndx: Int): seq[PNimrodNode] {.compiletime.} =
  result = @[]
  var params = pdNode[pdFormalParams]
  for i in fromIndx .. < params.len :
    if toIndx >= 0 and i > toIndx : break
    var p = params[i]
    if p.kind == nnkIdentDefs : 
      for k in 0 .. < p.len - 2: result.add(p[k])
    elif p.kind == nnkIdent or p.kind == nnkAccQuoted : result.add(p)
    
proc fullIdent* (node: PNimrodNode): String {.compiletime.} =
  case node.kind :
  of nnkIdent: result = $node.ident
  of nnkAccQuoted:
    result = ""
    for c in node.children :
      result &= $c.ident
  of nnkPostfix: result = node[1].fullIdent
  of nnkProcDef: result = node[pdIdent].fullIdent
  else : result = ""
  
proc indexOfPragma* (node: PNimrodNode, pragma: String): int {.compiletime.} =
  if node.kind == nnkProcDef :
    var pragma = !pragma
    var pnodes = node[pdPragma]
    for i in 0.. < pnodes.len  :
      if pnodes[i].ident == pragma : return i
  return -1
  
proc removePragma* (node: PNimrodNode, idx: Int) {.compiletime.} =
  if node.kind == nnkProcDef :
    var pnodes = node[pdPragma]
    if idx >= 0 and idx < pnodes.len : pnodes.del(idx)
    if pnodes.len == 0 : node[pdPragma] = newNimNode(nnkEmpty) 
       