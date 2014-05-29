#
#                  nimrod-tools
#        (c) Copyright 2013 Adrian Veith
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## This module implements a case insenstive string class

import strutils

type 
  IString* = distinct string

converter toIString* (x: string): istring = istring(x)


proc `$` * (x: istring): istring  {.borrow.}
proc `&` * (x: istring, y: char): istring  {.borrow.}
#proc `&` * (x: char, y: char): string  {.borrow.}
proc `&` * (x, y: istring): istring  {.borrow.}
proc `&` * (x: char, y: istring): istring  {.borrow.}

proc `&=`* (x: var istring, y: istring)  {.borrow.}
template `&=`* (x: var istring, y: char)  = x = x & y
template add*(x: var istring, y: char) = x &= y
proc add*(x: var istring, y: istring)  {.borrow.}
  
template `<` *(x, y: istring): bool = cmpIgnoreCase(string(x), string(y)) < 0 
template `<=` *(x, y: istring): bool = cmpIgnoreCase(string(x), string(y)) <= 0 
template `==` *(x, y: istring): bool = cmpIgnoreCase(string(x), string(y)) == 0 
template `>=` *(x, y: istring): bool = cmpIgnoreCase(string(x), string(y)) >= 0 
template `>` *(x, y: istring): bool = cmpIgnoreCase(string(x), string(y)) > 0 
template `!=` *(x, y: istring): bool = cmpIgnoreCase(string(x), string(y)) != 0 
proc cmp *(x, y: istring): int = cmpIgnoreCase(string(x), string(y))
  
proc cmpInline*(x, y: istring): int {.inline.} = cmpIgnoreCase(string(x), string(y))

when isMainModule :
  var s1, s2: istring = "abc"
    
  echo s1
  echo s2

  echo s1 == s2

  s1 = "ABC"
  echo s1, " == ", s2, ": ", s1 == s2
  echo s1 & "a" , " == ", s2 & "A" , ": ", s1 & "a" == s2 & "A"
    