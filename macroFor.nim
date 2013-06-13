import  
  macros

type
  TPattern = tuple
    patNode, resNode: PNimrodNode 

proc isEqual(n1, n2: PNimrodNode): bool {.compiletime.} =
  if n1.kind == nnkIdent and n2.kind == nnkIdent :
    #echo n1.ident, " same ", n2.ident
    return n1.ident == n2.ident
  if n1.len == n2.len and n1.kind == n2.kind :
    # echo n1.len, " same ", n2.len, " and ", n1.kind, " same ", n2.kind
    for i in 0 .. n1.len -1:
      if not isEqual(n1[i], n2[i]): return false
    return true
  return false

proc replace(n: PNimrodNode, pat: TPattern): PNimrodNode {.compiletime.} =
  if isEqual(n, pat.patNode):
    # echo n.repr, " == ", pat.patNode.repr
    return pat.resNode
  
proc forAll(node: PNimrodNode, pat: TPattern, call: proc(n: PNimrodNode, pat:TPattern): PNimrodNode ): PNimrodNode {.compiletime.} =
  result = node
  for i in 0 .. result.len -1:
    if result[i] != nil :
      var nres = call(result[i], pat) 
      if nres != nil:
        result[i] = nres
      else : 
        result[i] = forAll(result[i], pat, call)
      
macro macFor* (x:stmt): stmt {.immediate.} =
  result = newNimNode(nnkStmtList)
  let n = callsite()
  var patterns: seq[TPattern] = @[]
  var stm: PNimrodNode
  var maxPat = 0
  block ok:
    block error:
      #echo n.len
      if n.len > 2 : 
        for i in 1 .. n.len - 1:
          case n[i].kind 
          of nnkStmtList :
            stm = n[i]
            break
          of nnkInfix :
            if n[i][0].kind != nnkIdent or n[i][0].ident != !"->" or 
              n[i][1].kind != nnkIdent or
              n[i][2].kind != nnkBracket:
                break error
            if n[i][2].len > maxPat : maxPat = n[i][2].len 
            patterns.add((n[i][1], n[i][2]))
          else : break error
        break ok
    error "usage macFor C->[X,Y,Z] : C = 2 * C"
  for i in 0..maxPat-1:
    var stm1 = stm.copyNimTree
    for p in patterns:
      var pat = p.patNode
      var res = p.resNode[i mod p.resNode.len]
      # echo pat.repr, "-> ", res.repr
      stm1 = stm1.forAll((pat, res), replace)
    echo stm1.repr
    result.add(stm1)

when isMainModule:
  var 
    x, y, z: int      
    r,g,b: int
    
  macFor Cn ->[X, Y, Z], Dn->[Y,Z,X], Rn->[R,G,B]:
    Rn = Cn + Dn
    
  const
    CBaseShift = 8
    CBaseSize = 1 shl CBaseShift
    CBaseMask = CBaseSize - 1
    
  type
    TColor = tuple
      R,G,B,A: byte
  
  proc Gradient(c1, c2: TColor; k: float): TColor =
    var Ik = (K * CBaseSize.toFloat).toInt    
    macFor Col->[R,G,B,A]:
      Result.Col = Byte(int(c1.Col) + ((int(c2.Col) - c1.Col.int) * Ik) shr CBaseShift)

  