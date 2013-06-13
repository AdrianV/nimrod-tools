#
#                  nimrod-tools
#        (c) Copyright 2013 Adrian Veith
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## This module implements some routines for accessing double floats in binary

when true : 
  template i64* (v: float64): int64 = cast[int64](v) 

else :
  template i64* (v: float64): int64 =
    var x = v
    cast[ptr int64](addr x)[] 

when true :
  template f64* (v: int64): float64  = cast[float64](v) 

else :
  template f64* (v: int64): float64  = 
    var x = v
    cast[ptr float64](addr x)[] 

proc fillBits(bits: int): int64 {.compiletime.} =
  var x = 0
  for i in 0.. < bits : x = (x shl 1) or 1
  x

const
  BITS_SIGN = 1
  BITS_MANTISSA = 52
  BITS_EXPONENT = 64 - BITS_MANTISSA - 1 
  MAP_SIGN = 0x8000_0000_0000_0000
  MAP_MANTISSA = fillBits(BITS_MANTISSA) 
  MAP_EXPONENT = (0xFFFF_FFFF_FFFF_FFFF and not MAP_SIGN) and not MAP_MANTISSA
  NAN_EXPONENT = fillBits(BITS_EXPONENT)
  
type
  TMantissaRange = int64 #range[0..0xF_FFFF_FFFF_FFFF'i64]
  
proc buildFloat64(negativ: bool, exp: range[0..0x7FF], man: TMantissaRange): float64 {.inline.} =
  f64((exp.int64 shl BITS_MANTISSA) or man.int64 or (if negativ : MAP_SIGN else : 0))
   
proc negative* (d: Float): bool {.inline.} = (i64(d) and MAP_SIGN) != 0

proc binExponent* (d: Float): int {.inline.} = ((i64(d) and not MAP_SIGN) shr BITS_MANTISSA).int

proc exponent* (d: Float): int {.inline.} = ((i64(d) and not MAP_SIGN) shr BITS_MANTISSA).int - 1023

proc mantissa* (d: Float): int64 {.inline.} = (i64(d) and MAP_MANTISSA) 

proc isZero* (d: Float): bool {.inline.} = (i64(d) and not MAP_SIGN) == 0

proc isSubnormal* (d: Float): bool {.inline.} = 
  let i = i64(d) 
  return ((i and MAP_EXPONENT) == 0) and ((i and MAP_MANTISSA) != 0)

when isMainModule:

  import strutils, math
  
  echo negative(1.0)
  echo negative(-3.14)
  echo fillBits(3)
  echo MAP_EXPONENT.toBin(64)
  echo i64(-3.14).toBin(64)
  echo i64(-3.1415).toBin(64)
  echo "pi = 2^", exponent(3.14), " * ", mantissa(3.14)   
  echo i64(NaN).toBin(64)
  echo binExponent(NaN).toHex(4)
  echo mantissa(NaN).toHex(16)
  echo isZero(0.0)    
  echo isZero(-0.0)    
  echo exponent(2.0)  
  echo mantissa(2.0)
  echo "123456.0 e=", exponent(123456.0)
  echo "123456.0 m=", mantissa(123456.0)
  
  var d = buildFloat64(false, 0, 1024)
  var d2 = d + 1.1
  var d3 = 1.1 - d2 
  echo d3 == d, " delta ", d3 - d
  echo isZero(d)
  echo isSubnormal(d)
  d = buildFloat64(false, NAN_EXPONENT, 1024)
  