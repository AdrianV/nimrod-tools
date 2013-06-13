#
#                  nimrod-tools
#        (c) Copyright 2013 Adrian Veith
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## This module implements some routines for parsing

type
  TParseString* {.pure, final, shallow.} = object
    s*: string
    a*: int

template parseLoop* (x, it: expr, loop: stmt) : stmt {.dirty,immediate.} =
  block:
    var proceed {.noinit.}: bool 
    var `x` {.inject.} = current(it, proceed)
    while proceed :
      loop
      `x` = next(it, proceed)

proc current* (s: var TParseString, proceed: var bool): char {.inline.} =
  proceed = s.a < s.s.len
  return s.s[s.a]
  
proc next* (s: var TParseString, proceed: var bool): char {.inline.} =
  proceed = s.a < s.s.len
  if proceed : inc(s.a)
  result = s.s[s.a]

proc next* (s: var TParseString): char {.inline.} =
  if s.a < s.s.len : 
    inc(s.a)
  result = s.s[s.a]

proc prev* (s: var TParseString, proceed: var bool): char {.inline.} =
  proceed = s.a > 0
  if proceed : 
    dec(s.a)
    result = s.s[s.a]
  else: result = '\0'

proc prev* (s: var TParseString): char {.inline.} =
  if s.a > 0 : 
    dec(s.a)
    result = s.s[s.a]
  else: result = '\0'
  
  
proc fromLiteral* (s: string): TParseString {.inline.} =
  if not isNil(s) : result.s = s
  else: result.s = ""

proc fromLiteral* (s: string, start: int): TParseString {.inline.} =
  if not isNil(s) : result.s = s
  else: result.s = ""
  result.a = min(start, result.s.len)

proc fromString* (s: var string): TParseString {.inline.} =
  if not isNil(s) : shallowCopy(result.s, s)
  else: result.s = ""

proc fromString* (s: var string, start: int): TParseString {.inline.} =
  if not isNil(s) : shallowCopy(result.s, s)
  else: result.s = ""
  result.a = min(start, result.s.len)

proc `[]`* (s: TParseString, x): char {.inline.} = return s.s[s.a + x]

# proc `!`* (s: TParseString): char {.inline.} = return s.s[s.a -1]

proc len* (s: TParseString): int {.inline.} =
  return s.len - s.a
  
iterator items*(s: TParseString): char {.inline.} =
  for i in s.a .. s.s.high :
    yield s.s[i]  

#iterator mitems*(s: TParseString): var char {.inline.} =
#  for i in s.a .. s.s.high :
#    yield s.s[i]  

proc `$`* (s: TParseString): string {.inline.} = 
  return s.s.substr(s.a)    

proc substr* (s: TParseString, first: int): string {.inline.} =   
  return s.s.substr(s.a + first)    

proc substr* (s: TParseString, first, last: int): string {.inline.} =   
  return s.s.substr(s.a + first, s.a + last)    

proc slice* (s: TParseString, length: int): string {.inline.} =
  return s.s.substr(s.a, s.a + length -1)    

when isMainModule:

  var str = "12345678"
  var ps = fromString(str, 2)
  var p2 = ps
  
  echo ps.substr(2,3)
  echo ps.slice(4)

  str[2] = 'c'
  echo ps.substr(2,3)
  echo ps.slice(4)
  str = "abcdefghijk"
  echo ps.substr(2,3)
  echo ps.slice(4)

  echo p2.substr(2,3)
  echo p2.slice(4)

  p2.a = 3
  echo p2.substr(2,3), " <> ? ", ps.substr(2,3)
  
  ps = fromLiteral("abcdef", 2)
  echo ps.substr(2,3)
  echo ps.slice(4)

  parseLoop c, ps :
    echo c
  ps = fromLiteral("abcdef", 2)
  parseLoop c, ps :
    echo ps[0]
    c = ps.next
    echo c
  ps = fromLiteral("abcdef", 3)
  parseLoop c, ps :
    echo ps[0]
    c = ps.next
    echo c == '\0'
    
  ps = fromLiteral(nil, 3)
  parseLoop c, ps :
    echo c

  ps = fromLiteral("123", 3)
  parseLoop c, ps :
    echo c
  