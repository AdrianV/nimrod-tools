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

## The ``datetime`` module implements a freepascal/Delphi compatible TDateTime type.

import math, times, helper

type
  TDateTime* = float
  DateRec* = tuple
    day: Int
    month: Int
    year: Int
  DateTimeRec* = tuple
    date : DateRec
    hour: Int
    minute: Int
    sec: Float


const
  DateDelta = 693594
  D1 = 365
  D4 = D1 * 4 + 1
  D100 : int = D4 * 25 - 1
  D400 : int = D100 * 4 + 1
  HOURS*   : Float = 1 / 24
  MINUTES* : Float = 1 / (24 * 60)
  SECONDS* : Float = 1 / (24 * 60 * 60)
var  
  ISOFirstWeekDay*     : Int = 0  # Monday
  ISOFirstWeekMinDays* : Int = 4  # the first week of the year contains then 4.th January
  MD0 = [0, 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
  MD1 = [0, 31, 29, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]



proc isLeapYear* (year: Int): Bool {.inline.} =
  return (year mod 4 == 0) and ((year mod 100 != 0) or (year mod 400 == 0))


proc encode* (year: Int, month: Int, day: Int): Float =
  var DayTable = if (isLeapYear(year)) : addr MD1 else : addr MD0
    
  if ((year >= 1) and (year <= 9999) and (month >= 1) and (month <= 12) and 
    (day >= 1) and (day <= DayTable[][month])) :
      var I = 1
      var d = day
      while (I < month) :
        d += DayTable[][I]
        inc(I)
      var ym = year.toFloat - 1.0
      return (ym * 365.0 + Math.floor(ym / 4.0) - Math.floor(ym / 100.0) + Math.floor(ym / 400.0) + d.toFloat - DateDelta.toFloat)
  else :
    return 0.0
  

proc encodeTime* (hour: Int, minute: Int, sec: Float): Float {.inline.} =
  return ((hour.toFloat * HOURS) + minute.toFloat * MINUTES + sec * SECONDS)
  
proc encodeDateTime* (year: Int, month: Int, day: Int, hour: Int, minute: Int, sec: Float): Float {.inline.} =
  return (encode(year, month, day) + (hour.toFloat * HOURS) + minute.toFloat * MINUTES + sec * SECONDS)


proc decode* (me: Float): DateRec  =
  # if me == null :return ( day:0, month: 0, year: 0 )
  var T: Int = iTrunc(me) + DateDelta
  # if (Math.isNaN(T)) return { day:0, month: 0, year: 0 };
  if T <= 0 :
    return ( day: 0, month: 0, year: 0  )
  else :
    dec(T)
    var Y: Int = 1
    while T >= D400 :
      T -= D400
      Y += 400
    var I = T div D100
    var D = T mod D100
    if (I == 4) :
      dec(I)
      D += D100
    
    Y += I * 100
    I = D div D4
    D = D mod D4
    Y += I * 4
    I = D div D1
    D = D mod D1
    if I == 4 :
      dec(I)
      D += D1
    Y += I
    var DayTable = if isLeapYear(Y) : addr MD1 else: addr MD0
    var M = 1
    while true :
      I = DayTable[M]
      if D < I : break
      D -= I
      inc(M)
    
    return (day: D + 1, month: M, year: Y )


proc year* (me: Float): Int {.inline.} =
  return decode(me).year

proc month* (me: Float): Int {.inline.} =
  return decode(me).month

proc day* (me: Float): Int {.inline.} =
  return decode(me).day

proc lastDayOf* (Month: Int, Year: Int): Int {.inline.} =
  return if isLeapYear(Year) : MD1[Month] else : MD0[Month]


proc lastDayOfMonth* (me: Float): Int =
  let dt = decode(me)
  return lastDayOf(dt.month, dt.year)


proc dayOfWeek* (me: Float): Int =
  # Mo = 0; Sun= 6
  return (iTrunc(me) + 5) mod 7


proc fixDay* (me: Float, day: Int): Float =
  let dt: DateRec = decode(me)
  return encode(dt.year, dt.month, day)


proc ISOWeekNumber* (me: Float) : tuple[Week: int, Year: int, WeekDay: int] =
  #var YearOfWeekNumber, WeekDay: Integer): Integer;
  var WeekDay : Int = ((dayOfWeek(me) - ISOFirstWeekDay + 7) mod 7) + 1
  var day4: Float = me - (WeekDay - 8 + ISOFirstWeekMinDays).toFloat
  var dt: DateRec = decode(day4)
  return ( Week: iTrunc((day4 - encode(dt.year, 1, 1)) / 7.0) +1, Year: dt.year, WeekDay: WeekDay )


proc weekNumber* (me: Float): Int {.inline.} =
  return ISOWeekNumber(me).Week

proc timeValue* (me: Float): Float =  return me - Math.floor(me)

proc decodeDateTime* (me: Float): DateTimeRec =
  result.date = decode(me)
  var t = min(1.0 - 0.00005 * SECONDS, timeValue(me) + 0.00005 * SECONDS) * 24.0
  result.hour = iTrunc(t)
  t = (t - result.hour.toFloat) * 60.0
  result.minute = iTrunc(t)
  t = (t - result.minute.toFloat) * 60.0
  result.sec = t
  # return (year: dt.year, month: dt.month, day: dt.day, hour: h, minute: m, sec: Tools.round(t, 3) };


proc toTTimeInfo* (me: Float): TTimeInfo =
  let dt: DateTimeRec = decodeDateTime(me)
  result.year = dt.date.year
  result.month = cast[TMonth](dt.date.month -1)
  result.monthday = dt.date.day
  result.hour = dt.hour
  result.minute = dt.minute
  result.second = Math.round(dt.sec)
  result.weekDay = cast[TWeekDay](dayOfWeek(me))


proc EasterSunday* (year: Int): TDateTime = 
  var a :Int = year mod 19
  var b : Int = (204 - 11 * a) mod 30
  if b == 28 or b == 29 : dec(b)
  var c: Int = (year + year div 4 + b - 13) mod 7
  var day : Int = 28 + b - c - 2
  var month : Int = 3
  if (day > 31) :
    day -= 31
    month = 4
  return encode(year, month, day)


proc fromTTimeInfo* (d: TTimeInfo): TDateTime =
  return encodeDateTime(d.year, Ord(d.month), Ord(d.monthday), d.hour, d.minute, d.second.toFloat)

  
proc now* (): TDateTime  =
  return fromTTimeInfo(getLocalTime(getTime()))

when isMainModule:

  var dt = encode(2012, 7, 23)

  
  echo dt.decodeDateTime().repr
  dt = encode(2013,1,1)
  echo dt.toTTimeInfo
