template binSearchStrictImpl *(len: expr, less, equal: expr, result: expr): stmt {.immediate.}  =
  result = 0
  var H = len -1
  block search :
    while result <= H :
      let I = (result + H) shr 1
      if less(I) : result = I + 1
      elif equal(I) :
        result = I + 1
        break search 
      else:
        H = I - 1
    result = - result

template binSearchImplLitStrict *(haystack, result: expr, hay_i: stmt): stmt =
  result = 0
  var H = haystack.len -1
  while result <= H :
    if H - result <= 3 :
      #echo "linear search ", needle, " from ", result, " to ", H
      var I = result
      while I <= H :
        let left = hay_i(I) 
        if left < needle : inc(I)
        elif left == needle : return I + 1
        else : break
      return - I
    else :
      let I = (result + H) shr 1
      let left = hay_i(I) 
      if left < needle: result = I + 1
      elif left == needle: return I + 1 
      else:
        H = I - 1
  result = - result

template binSearchImpl *(hay_len, result: expr, docmp: expr): stmt =
  # type TE type(T[0])
  var bFound = false
  result = 0
  var H = hay_len -1
  when false : #if H < 8 : # H < 8 
    while result <= H :
      let I = result
      var SW = docmp(I) 
      if SW < 0: result = I + 1 
      else:
        if SW == 0: inc(result)
        else: result = -result
        return
    return - result
  else :
    while result <= H :
      var I = (result + H) shr 1
      var SW = docmp(I) 
      if SW < 0: result = I + 1 
      else:
        H = I - 1
        if SW == 0 : bFound = True
    if bFound: inc(result)
    else: result = - result
  
proc binSearch* [T] (haystack: openarray[T], needle:T): Int =
  template compare(I): int = haystack[I].cmp(needle)
  binSearchImpl(haystack.len, result, compare)

proc binSearchStrict* [T] (haystack: openarray[T], needle:T): Int =
  var SW : int
  template less(I: expr): bool = 
    SW = haystack[I].cmp(needle)
    SW < 0
  template equal(I: expr): bool = 
    SW == 0
  binSearchStrictImpl(haystack.len, less, equal, result)



when isMainModule:
  var hay : array[0..1000, int]
  for i in 0..hay.high : hay[i] = i
  
  echo binSearch(hay, 14)
  
  #when true:  

  echo binSearch(hay, 1)
  echo binSearch(hay, 2)  
  echo binSearch(hay, 3)    
  echo binSearch(hay, 575)    
  echo binSearchStrict(hay, 576)    

  for i in 0 .. hay.high :
    var y = binSearchStrict(hay, i)
    if y <= 0:
      echo "not found: ", i
    if y > 0 and y - 1 != i :
      echo "wrong pos :", y, " for ", i
      