#
#                  nimrod-tools
#        (c) Copyright 2013 Adrian Veith
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## This module implements some compiletime traits

template isNilable* (typ: typedesc): bool =
  (typ is string) or (typ is proc) or (typ is ref) or (typ is ptr) #or (typ is seq)


when isMainModule:

  type
    TTest[T] = object
      v: T
      when  isNilable(T) :
        test: Bool

  var t: TTest[string]
  t.test = true        

  var t2: TTest[int]
  t2.test = false   # should fail