#
#                  nimrod-tools
#        (c) Copyright 2013 Adrian Veith
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## This module implements a dynamic class which 
## can be null, boolean, integer, float, string
## an array of these values, or an object of these values
## it parses a json string or can be converted to a json string

import math, lazybtree, strutils, helper, helperParse, forLoops

type
  TDynType = enum
    dtNull,
    dtFalse,
    dtTrue,
    dtInt,
    dtFloat,
    dtString,
    dtArray,
    dtObject
  TDynamic* = ref object {.inheritable, pure.}
    t : TDynType
  TDynamicInt* = ref object of TDynamic
    Value* : int
  TDynamicFloat* = ref object of TDynamic
    Value* : float
  TDynamicString* = ref object of TDynamic
    Value* : string
  TDynamicArray* = ref object of TDynamic
    Value* : seq[TDynamic]
  TDynamicObject* = ref object of TDynamic
    Value* : PBTree[string, TDynamic]
    FCaseInsensitive: bool
  TPathType = object
    case isInt: bool :
    of false : vString: string
    of true : vInt: int
  TDynPath = object
    v: ptr TDynamic
    path: seq[TPathType]
      
proc toPath* (v: int): TPathType {.inline.} = 
  doAssert(v >= 0, "only positive index allowed")
  result.isInt = true
  result.vInt = v
  
proc toPath* (v: string): TPathType {.inline.} = 
  result.vString = v
      
template getPathImpl() : stmt {.immediate.} = 
  # var result {.gensym.} : TDynPath
  result.v = cast[ptr TDynamic](addr(v))
  newSeq(result.path, data.len +1)
  result.path[0] = first.toPath()
  for i in 0.. data.len-1 : result.path[i+1] = data[i]
      
proc `{}`* [T:int|string] (v: var TDynamic, first: T, data: varargs[TPathType, toPath]): TDynPath =
  getPathImpl()

proc `:=`* (v: var TDynamic, val: TDynamic) {.inline.} =
  v = val

proc dynamic* (v: bool): TDynamic {.inline.} =
  new(result)
  result.t = if v: dtTrue else: dtFalse

proc dynamic* (v: int): TDynamicInt {.inline.} =
  new(result)
  result.t = dtInt
  result.Value = v

proc dynamic* (v: float): TDynamicFloat {.inline.} =
  new(result)
  result.t = dtFloat
  result.Value = v
  
proc dynamic* (v: string): TDynamicString {.inline.} =
  new(result)
  result.t = dtString
  result.Value = v

proc dynamicArray* (len: int = 0): TDynamicArray {.inline.} =
  new(result)
  result.t = dtArray
  newSeq(result.Value, len)

proc dynamicObject* (ACaseInsensitive: Bool = false): TDynamicObject {.inline.} =
  new(result)
  result.t = dtObject
  result.FCaseInsensitive = ACaseInsensitive
      
proc `:=`* [T:int|float|string|bool] (v: var TDynamic, val: T) {.inline.} =
  v = dynamic(val)
    
proc `:=`* (v: TDynPath, val: TDynamic) =
  var cur = v.v
  for i in  0..v.path.len -1:
    if v.path[i].isInt :
      if cur[] == nil or cur[].t != dtArray :
        cur[] = dynamicArray()
      var va = cast[TDynamicArray](cur[])
      let idx = v.path[i].vInt
      if va.Value.len <= idx : setLen(va.Value, idx +1)
      cur = addr(va.value[idx])
    else :
      if cur[] == nil or cur[].t != dtObject :
        cur[] = dynamicObject()
      var vo = cast[TDynamicObject](cur[])
      let idx = v.path[i].vString
      let it = vo.value.findOrInsert(idx)
      cur = addr(it.value)
  cur[] = val

proc `:=`* [T:int|float|string|bool] (v: TDynPath, val: T) {.inline.} =
  v := dynamic(val)

template walkPath(path: expr): stmt {.immediate.} =
  for i in  0..path.len -1:
    if path[i].isInt :
      if result == nil or result.t != dtArray : return nil
      var va = cast[TDynamicArray](result)
      let idx = path[i].vInt
      if idx < 0 or idx >= va.Value.len : return nil
      result = va.value[idx]
    else :
      if result == nil or result.t != dtObject : return nil
      var vo = cast[TDynamicObject](result)
      let idx = path[i].vString
      let it = vo.value.find(idx)
      if it == nil : return nil
      result = it.value

proc `[]`* (v: TDynamic, path: varargs[TPathType, toPath]): TDynamic =
  result = v
  walkPath(path)
  when false :  
    for i in  0..path.len -1:
      if path[i].isInt :
        if result == nil or result.t != dtArray : return nil
        var va = cast[TDynamicArray](result)
        let idx = path[i].vInt
        if idx < 0 or idx >= va.Value.len : return nil
        result = va.value[idx]
      else :
        if result == nil or result.t != dtObject : return nil
        var vo = cast[TDynamicObject](result)
        let idx = path[i].vString
        let it = vo.value.find(idx)
        if it == nil : return nil
        result = it.value

converter toDynamic* (v: TDynPath) : TDynamic =
  result = v.v[]
  # echo result.repr, " ", v.path.repr
  walkPath(v.path)


template getValue(v: expr, typ: typedesc): expr {.immediate.} =
  cast[`TDynamic typ`](v)[].Value

proc asIntSlow (v: TDynamic): int =
  if v != nil :
    case v.t :
    of dtNull, dtFalse: return 0
    of dtTrue: return 1
    of dtInt : return getValue(v, int)
    of dtFloat: return getValue(v, float).toInt
    of dtString: return parseInt( getValue(v, string))
    of dtArray: return 0
    of dtObject: return 0
  else : return 0

proc asFloatSlow (v: TDynamic): float =
  if v != nil :
    case v.t :
    of dtNull, dtFalse: return 0.0
    of dtTrue: return 1.0
    of dtInt : return getValue(v, int).toFloat
    of dtFloat: return getValue(v, float)
    of dtString: return parseFloat( getValue(v, string))
    of dtArray: return 0.0
    of dtObject: return 0.0
  else : return 0.0

proc QuotedString(s: string): String =
  Result = "\""
  for c in s : 
    case c : 
    of '\x00' .. '\x07', '\x0B', '\x0C', '\x0E' .. <' ' : Result &= "\\u" & ToHex(Ord(C), 4)
    of '\x08' : Result &= "\\b"
    of '\x09' : Result &= "\\t"
    of '\x0A' : Result &= "\\n"
    of '\x0D' : Result &= "\\r"
    of '\\' : Result &= "\\\\"
    of '\"' : Result &= "\\\""
    else :
      Result.add(c)        
  Result.add('"')

proc asArray* (v: TDynamic): TDynamicArray {.inline.} =
  return if v != nil and v.t == dtArray : cast[TDynamicArray](v) else: nil

proc asObject* (v: TDynamic): TDynamicObject {.inline.} =
  return if v != nil and v.t == dtObject : cast[TDynamicObject](v) else: nil

proc asString* (v: TDynamicArray): string 
proc asString* (v: TDynamicObject): string 
proc `$`* (v: TDynamic): string {.inline.} 

proc asJSONString(v: TDynamic): string =
  if v != nil :
    case v.t :
    of dtNull : return "null"
    of dtFalse: return "false"
    of dtTrue: return "true"
    of dtInt : return $getValue(v, int)
    of dtFloat: return $getValue(v, float)
    of dtString: return QuotedString(getValue(v, string))
    of dtArray: return asString(asArray(v))
    of dtObject: return asString(asObject(v))
  else : return "null"

 
proc asStringSlow (v: TDynamic): string =
  if v != nil :
    case v.t :
    of dtNull : return ""
    of dtFalse: return "false"
    of dtTrue: return "true"
    of dtInt : return $getValue(v, int)
    of dtFloat: return $getValue(v, float)
    of dtString: return getValue(v, string)
    of dtArray: return asString(asArray(v))
    of dtObject: return asString(asObject(v))
  else : return ""

proc asBoolSlow (v:TDynamic): bool =
  return v != nil and (v.t == dtTrue or 
    (v.t == dtInt and getValue(v,int) > 0) or
    (v.t == dtFloat and getValue(v, float) > 0.0) or  
    (v.t == dtString and getValue(v, string) == "true" ))
    
proc asInt* (v: TDynamic): int {.inline.} =
  if v != nil and v.t == dtInt : return getValue(v, int)
  else : return asIntSlow(v)

proc asFloat* (v: TDynamic): float {.inline.} =
  if v != nil and v.t == dtFloat : return getValue(v, float)
  else : return asFloatSlow(v)

proc asString* (v: TDynamic): string {.inline.} =
  if v != nil and v.t == dtString : return getValue(v, string)
  else : return asStringSlow(v)

proc asBool* (v: TDynamic) : Bool {.inline.} =  
  return v != nil and (v.t == dtTrue or asBoolSlow(v))
  
proc typeOf(v: TDynamic): TDynType {.inline.} =
  return if v != nil: v.t else: dtNull

proc `$`* (v: TDynamic): string = 
  return asString(v)
    

template enterCheckForRecursion(default: string) =
  var recursive {.global, threadvar, inject.} : PBtree[TDynamic, string]
  var call_level {.global, threadvar, inject.} : int
  if call_level == 0:
    recursive[v] = default
  else :
    result = recursive[v]
    if not isNil(result):
      #echo "recursive: (",result.len, ") ", result
      if result.len == 2: # [] or {}
        let s = "{ \"__recursive__\": \"" & cast[TAddress](v).toHex(2 * sizeof(TAddress)) & "\"}" 
        if result[0] == '[' :
          result = result[0] & s & result[1]
        else :          
          result = s
        # echo result
      return
  inc(call_level)

template addRecursiveChecked(res, val: expr): stmt =
  when true:
    res.add(val.asJSONString)
  when false:  # not needed, but faster when the structure is recursive
    var t = typeof(val)
    if t in {dtArray, dtObject} :
      var s = lazybtree.getValue(recursive, val)
      if isNil(s) :
        s = val.asJSONString
        recursive[val] = s
      res.add(s)
    else : res.add(val.asJSONString) 


template leaveCheckForRecursion() =
  dec(call_level)
  if call_level == 0:
    recursive = nil


proc len* (v: TDynamicArray) : int {.inline.} =
  return if v != nil: v.Value.len else: 0

proc add* (v: TDynamicArray, val: TDynamic): int =
  if v != nil :
    result = v.Value.len
    setLen(v.Value, result + 1)
    v.Value[result] = val
    return
  return -1

proc `[]`* (v: TDynamicArray, i: int): TDynamic {.inline.} =
  if v != nil and i >= 0 and i < v.Value.len: return v.Value[i] 
  return nil

proc `[]=`* (v: TDynamicArray, i: int, val: TDynamic) {.inline.} =
  if v != nil and i >= 0 :
    if i >= v.Value.len: setLen(v.Value, i + 1)
    v.Value[i] = val

proc `[]=`* [T:int|float|string|bool] (v: TDynamicArray, i: int, val: T) {.inline.} =
  v[i] = dynamic(val)

proc `{}`* (v: var TDynamicArray, first: string, data: varargs[TPathType, toPath]): TDynPath =
  {.error.}

when true :  
  proc `{}`* (v: var TDynamicArray, first: int, data: varargs[TPathType, toPath]): TDynPath =
    doAssert(first >= 0, "only positive index allowed")
    when true :
      # if v == nil : v = dynamicArray()
      getPathImpl()
    else :
      if v == nil : v = dynamicArray()
      if first >= v.Value.len: setLen(v.Value, first + 1)
      result.v = addr(v.Value[first])
      newSeq(result.path, data.len)
      for i in 0.. data.len-1 : result.path[i] = data[i]

iterator items* (v: TDynamicArray): TDynamic {.inline.} =
  for i in 0 .. v.Value.high:
    yield v.Value[i]

proc asString* (v: TDynamicArray): string =
  enterCheckForRecursion("[]")
  result = "["
  for x in 0 .. < v.len :
    if x > 0: result.add(',')
    addRecursiveChecked(result, v[x])
  result.add(']')
  leaveCheckForRecursion()
    
proc `[]`* (v: TDynamicObject, i: string): TDynamic =
  if v != nil :
    let key = if not v.FCaseInsensitive : i else : toLower(i)
    let it = Find(v.Value, key)
    if it != nil : return it.Value
  return nil

proc `{}`* (v: var TDynamicObject, first: int, data: varargs[TPathType, toPath]): TDynPath =
  {.error.}

when true:  
  proc `{}`* (v: var TDynamicObject, first: string, data: varargs[TPathType, toPath]): TDynPath =
    when true:
      getPathImpl()
      #result.v = cast[ptr TDynamic](addr(v))
      #newSeq(result.path, data.len +1)
      #result.path[0] = first.toPath()
      #for i in 0.. data.len-1 : result.path[i+1] = data[i]
    else :
      if v == nil : v = dynamicObject()
      let key = if not v.FCaseInsensitive : first else : toLower(first)
      let it = FindOrInsert(v.Value, key)
      if it.value == nil or it.value.t != dtObject : it.value = dynamicObject()
      result.v = addr(it.value)
      newSeq(result.path, data.len)
      for i in 0.. data.len-1 : result.path[i] = data[i]

proc `[]=`* (v: var TDynamicObject, i: string, val: TDynamic) =
  if v == nil : v = dynamicObject()
  let key = if not v.FCaseInsensitive : i else : toLower(i)
  v.Value[key] = val

proc `[]=`* [T:int|float|string|bool] (v: var TDynamicObject, i: string, val: T) {.inline.} =
  v[i] = dynamic(val)

proc keys* (v: TDynamicObject): TIteratorKeys[string, TDynamic] = 
  return v.Value.Keys
proc values* (v: TDynamicObject): TIteratorValues[string, TDynamic] = 
  return v.Value.values
proc pairs* (v: TDynamicObject): TIteratorPairs[string, TDynamic] = 
  return v.Value.pairs

iterator keys* (v: TDynamicObject): string {.inline.} =
  forLoop e, v.Value.keys : yield e

iterator values* (v: TDynamicObject): TDynamic {.inline.} =
  forLoop e, v.Value.values : yield e

iterator pairs* (v: TDynamicObject): tuple[key:string, val: TDynamic] {.inline.} =
  forLoop e, v.Value.pairs : yield e

  
proc asString* (v: TDynamicObject): string =
  enterCheckForRecursion("{}")
  var res = "{"
  var first = true
  forEach v.Value, proc(key: string, val: TDynamic) = 
    # echo key, "= ", typeof(val), ": ", val
    if not first :
      res.add(',')
    first = false
    res.add(QuotedString(key))
    res.add(": ")
    addRecursiveChecked(res, val)
  
  res.add('}')
  leaveCheckForRecursion()
  return res

{.push overflowChecks: off.}
proc ParsePosInt(s: var TParseString) : Int = 
  # Result:= s;
  # Result = 0 
  parseLoop c, s:
    case c:
    of '0'..'9': 
        let newVal = (result * 10) + (Ord(c) - Ord('0'))
        if newVal < result :
          discard prev(s)
          return
        result = newVal
    else: break
{.pop.} # overflowChecks

proc ParseNumber(s: var TParseString): TDynamic =
  # type
  #  NumberFlag = enum nfNegative, nfDouble, nfExponent, nfNegExp
  #  NumberFlags = set of NumberFlag
  #  iVal: Integer;
  # dVal, dez: Double;
  # bNegative: Boolean;

  # Result:= s;
  # Result = nil
  var bNegative = false
  if s[0] == '-' :
    bNegative = true
    discard s.next
  var dVal = 0.0
  var iVal = ParsePosInt(s)
  if bNegative :
    iVal = -iVal
  case s[0] :
    of '0'..'9','.','E','e': 
      dVal = iVal.toFloat
    else : return dynamic(iVal)
  iVal = 0
  var dez = 0.0
  parseLoop c, s :
    case c :
    of '0'..'9': 
      if dez == 0.0 :
        dVal = (dVal * 10.0) + toFloat(Ord(c) - Ord('0'))
      else:
        dVal = dVal + toFloat(Ord(c) - Ord('0')) / dez
        dez = dez * 10.0
    of '.': 
      #echo "dot ", dval
      if dez == 0.0 :
        dez = 10.0
      else: 
        # ? indicate error to upper call ?
        return
    of 'E', 'e': 
      #echo "e ", dval
      c = s.next()
      bNegative = False
      if (c == '-') or (c == '+') :
        bNegative = c == '-'
        c = s.next()
      case c :
      of '0'..'9': 
          iVal = ParsePosInt(s)
          if bNegative :
            iVal = -iVal
          if iVal != 0 :
            dVal = dVal * IntPower(10, iVal)
          break
      else : return
    else : break
  #echo dval
  return dynamic(dval)

proc ParseStringVal(s: var TParseString) : string =
  #var first = s.a
  var str = ""
  var cQuote = s[0]
  discard s.next()
  parseLoop c, s:
    if c == cQuote :
      discard s.next()
      return str
    elif c == '\\' :
      c = s.next()
      case c :
      of '\0' : return
      of '\\' : str.add('\\')
      of '\"' : str.add('\"')
      of '\'' : str.add('\'')
      of 'n'  : str.add('\x0A')
      of 'r'  : str.add('\x0D')
      of 't'  : str.add('\9')
      of 'b'  : str.add('\8')
      of 'u'  : 
        var x = 0
        for i in 1..4:
          c = s.next()
          case c :
          of  '0' .. '9' : x = (x shl 4) or (ord(c) -ord('0'))
          of  'A' .. 'F' : x = (x shl 4) or (ord(c) -ord('A') + 10)
          of  'a' .. 'f' : x = (x shl 4) or (ord(c) -ord('a') + 10)
          else : return  
        str.add(chr(x and 0xFF))
        x = x shr 8
        if x != 0 :  
          str.add(chr(x and 0xFF))
      else : return
    else :
      str.add(c)
  

proc ParseString(s: var TParseString): TDynamic {.inline.} = 
  var str = ParseStringVal(s)
  if str != nil:
    result = dynamic(str)

proc ParseToken(s: var TParseString) : string = 
  result = ""
  parseLoop c, s:
    case c: 
    of '_','A'..'Z', 'a'..'z', '0'..'9': result.add(c)
    else : break

proc ParseBool(s: var TParseString) : TDynamic =
  var str = ParseToken(s)
  if str == "true"    : return dynamic(true)
  elif str == "false" : return dynamic(false)

proc ParseNull(s: var TParseString) : TDynamic =
  if ParseToken(s) == "null" :
    new(result)

proc ParseAny* (s: var TParseString, ACaseInsensitive: Bool) : TDynamic 

proc skipWS (s: var TParseString, c: var char) : bool {.inline.} =
  # echo "skip=", c
  while c != '\0' :
    # echo c
    case c :
    of '\1' .. ' ' : nil
    else : return true
    c = s.next()    
  return false

proc ParseArray(s: var TParseString, ACaseInsensitive: Bool) : TDynamic =
  var dyn = dynamicArray()
  # echo s[0]
  discard s.next()
  parseLoop c, s:
    if not skipWS(s, c) : break
    if c == ']' :
      discard s.next
      return dyn
    # echo "start array=", c
    var de = ParseAny(s, ACaseInsensitive)
    # echo de != nil
    if de == nil: break
    discard dyn.add(de)
    c = s[0]
    if not skipWS(s, c) : break
    # echo "delim=", c
    case c :
    of ',': nil
    of ']': 
      discard s.next()
      return dyn
    else: break
  dyn = nil

  
proc ParseObject(s: var TParseString, ACaseInsensitive: Bool) : TDynamic =
  #echo "start=", s[0]
  var dyn = dynamicObject(ACaseInsensitive)
  var name: string
  discard s.next()
  parseLoop c, s :
    if not skipWS(s, c) : break
    #echo "sym=", c
    case c : 
    of '"': 
      name = ParseStringVal(s)
      if name == nil: break
    of 'A'..'Z', 'a'..'z','_': name = ParseToken(s)
    of '}' : 
      discard s.next()
      return dyn
    else : break
    #echo "name=", name
    if name == "" : break
    c = s[0]
    if not skipWS(s, c) : break
    if c != ':' : break
    c = s.next()
    if not skipWS(s, c) : break
    # echo "sym3=", c
    var de = ParseAny(s, ACaseInsensitive)
    # echo "any=", de == nil, " ", s.repr
    if de == nil : break
    dyn[name] = de
    c = s[0]
    # echo dyn[name], " next= ", c
    if not skipWS(s, c) : break
    case c :
    of ',': nil
    of '}': 
      discard s.next()
      # echo "next=", s[0]
      return dyn
    else: break
  dyn = nil

proc ParseAny* (s: var TParseString, ACaseInsensitive: Bool) : TDynamic =
  #echo s[0]
  var c = s[0]
  if not skipWS(s, c) : return 
  case c :
  of '-', '0'..'9': result = ParseNumber(s)
  of '\"', '\'' : result = ParseString(s)
  of '{': result = ParseObject(s, ACaseInsensitive)
  of '[': result = ParseArray(s, ACaseInsensitive)
  of 'f', 't': result = ParseBool(s)
  of 'n' : result = ParseNull(s)
  else: nil
  if result == nil :
    echo "error at: ", s.substr(0, 100)

proc fromString* (s: var string, ACaseInsensitive: Bool = false): TDynamic {.inline.} =
  var ps = helperParse.fromString(s)
  return ParseAny(ps, ACaseInsensitive)

proc fromLiteral* (s: string, ACaseInsensitive: Bool = false): TDynamic {.inline.} =
  var ps = helperParse.fromLiteral(s)
  return ParseAny(ps, ACaseInsensitive)
  
proc `[]` * (v: TDynamic, key: int): TDynamic =
  if v != nil :
    case v.t :
    of dtArray: return cast[TDynamicArray](v)[key]
    of dtObject: return cast[TDynamicObject](v)[$key]
    else : nil
    
proc `[]` * (v: TDynamic, key: string): TDynamic {.inline.} =
  if v != nil and v.t == dtObject :
    return cast[TDynamicObject](v)[key]

proc `[]` * (v: TDynamic, key, key2: string): TDynamic =
  if v != nil and v.t == dtObject :
    return cast[TDynamicObject](v)[key][key2]

  
 
when isMainModule:
  
  var d = dynamicObject()
  d["hallo"] = "welt"
  echo d["hallo"]
  d["hallo"] = 123
  echo d["hallo"]
  echo d
  var a = dynamicArray()
  echo a.Value.len
  for i in 1 .. 20 :
    a[i] = i * i

  echo "a =", a
  
  a[10] = d
  a[11] = "1234"

  a{9, "test"} := "test ok"
  echo "a =", a

  #forLoop i, d.pairs:
  #  echo i.key, " ", i.value

  d["v"] = 3.14
  echo d["v"]
  echo "d =", d

  d["a"] = a
  echo "d =", d
  d["a2"] = a
  d["d"] = d
  echo "d =", d
  
  a[0] = a
  echo a
  echo "d=", d
  #echo fromLiteral ("{a: 123}")
  echo "bug ?", $d
  echo "d lit=", fromLiteral($d)
  echo "empty ?"
  for it in d.pairs : echo it
  echo d["d","a",1]
  echo " ", d["d","a",1]
  #d{"cc","dd"} := dynamic(12)
  echo d["cc","dd"]
  d["a"] = nil
  var d2: TDynamicObject
  d2{"test","blah"} := 123
  # d2{123,"blah"} := 123
  echo "wo bin ich", d2
  echo d{"cc1","D"}.repr
  d{"cc1","D"} := 234
  d{"cc1","D","e"} := 234
  d{"test","abc", 2} := "ok"
  echo "d = ", d
  
    
  var dx: TDynamic
  dx := "hallo"
  dx{"abc",2,3, "welt"} := 12
  
  echo "all: ", dx
  echo "abc: ", dx["abc"]
  echo "abc, 2: ", dx["abc",2]
  echo "abc, 2, 3: ", dx["abc",2,3]
  echo "abc, 2, 3, welt: ", dx["abc",2,3, "welt"]
  echo dx{"abc",2,3, "welt"}.toDynamic
  
  # dx{-1} := 3.14
  
  echo dx[1]
  
  echo "?" ,d["xyz", 1,2,3]
  #d = dx{"abc", 2}

  echo "??", d{"a2", 3}.toDynamic
  dx{"cde"} := d{"a2",3}
  echo dx
  when false:
    for i in a:
      echo i

    a = dynamicArray()
    a[0] = 123
    a[1] = "abc"
    a[3] = true
    a[4] = false
    a[5] = nil
    a[6] = a    
    echo a
    
    echo 1, "=", fromLiteral("1")
    echo "abc", "=", fromLiteral("\"abc\"")  
    echo fromLiteral ("{}")
    echo fromLiteral ("{a: 123}")
    echo fromLiteral ("{\"abc\": 123}")
    echo "bug 1 ", fromLiteral ("{ }")
    echo "bug 2 ", fromLiteral ("{  a    : 123}")
    echo "bug 3 ", fromLiteral ("{ \"abc\"      : 1234, b:5}")
    #echo "bug", fromLiteral ("[{}]")
    #echo fromLiteral ("[{a: 123}]")
    #echo fromLiteral ("[{\"abc\": 123}, 2, []]")
    #echo dynamicArray()
    echo fromLiteral ("[]")
    echo "no bug", fromLiteral ("[{}]")
    echo fromLiteral ("[{a: 123}]")
    echo fromLiteral ("[{\"abc\": 123}, 2, [] , \"hallo\",   1  ,]")
    
    