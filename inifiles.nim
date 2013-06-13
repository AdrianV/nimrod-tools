#
#                  nimrod-tools
#        (c) Copyright 2013 Adrian Veith
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## This module implements a Object Pascal like TIniFile 
## class, unlike the original it uses a fast btree
## and respects comments

import strutils, igncasestr, lazybtree, forloops, os

type
  TKeyInfo = tuple
    x: int
    delim: int
  TSecInfo = tuple
    name: string
    lines: seq[string]
    keys: PBTree[istring, TKeyInfo]
  TIniFile* = ref object
    sections: seq[TSecInfo]
    keys: PBTree[istring, int]
    space: tuple[indent, before, after: int]
    filename* : string
    
proc Index(it:ref TItem[istring, int]): int {.inline.} = it.value - 1

proc setIndex(it:ref TItem[istring, int], value: int) {.inline.} = 
  it.value = value + 1 
    
proc clean(o: var TKeyInfo) {.inline.} = nil
    
proc setFormat* (self: TIniFile, space: tuple[indent, before, after: int]): TIniFile {.discardable.} =
  self.space = space
  return self
      
proc keyAdd(self: TIniFile, line: string, xSec: int) {.inline.} =
  self.sections[xSec].lines.add(line)
  if line[0] == ';' or line[0] == '#' :
    return
  let p = line.find('=')
  if p >= 0 :      
    self.sections[xSec].keys[line.substr(0, p -1).strip] = (self.sections[xSec].lines.high, p+1)
       
proc lineAdd(self: TIniFile, line: string, xSec: var int) =
  #var line = line.strip
  var p: int
  var isSection = line[0] == '['
  var sName: string 
  if isSection :
    p = line.find(']')
    if p > 0 :
      sName = line.substr(1, p-1)
    else : 
      isSection = false
  template addSection() =
    #sName = sName.toLower
    var it = self.keys.findOrInsert(sName)
    xSec = it.index
    if xSec < 0 :
      self.sections.add((name: sName, lines: @[], keys: nil))
      xSec = self.sections.high
      it.setIndex(xSec)
  if self.sections == nil :
    if not isSection: sName = ""
    self.sections = @[]
    addSection()    
    if isSection : return
  if isSection :
    addSection()
  else :
    self.keyAdd(line, xSec)
    
proc finalCreate(self: TIniFile) {.inline.} =
  if isNil(self.sections): self.sections = @[]
    
proc fromString* (data: string): TIniFile =
  new(result)
  var x = 0
  for s in data.splitLines :
    result.lineAdd(s, x)
  result.finalCreate()
    
proc fromFile* (name: string): TIniFile =
  new(result)
  result.filename = name
  if existsFile(name):
    var x = 0
    for s in name.lines :
      result.lineAdd(s, x)
  result.finalCreate()
    
    
proc readKey* (self: TIniFile, sec, key: string, default: string = ""): string =
  let it = self.keys.Find(sec.istring)
  if not isNil(it) :
    let idx = it.index
    let itk = self.sections[idx].keys.Find(key.istring)
    if not isNil(itk) : return self.sections[idx].lines[itk.value.x].substr(itk.value.delim).strip
  return default

template parseOrDefault(s: string, parse: expr, default: expr) {.immediate.} =
  if s != "" :
    try :
      result = parse(s)
    except EInvalidValue :
      result = default
  else :
    result = default
      
proc readBool* (self: TIniFile, sec, key: string, default: Bool = false): Bool =
  parseOrDefault(self.readKey(sec, key), parseBool, default)

proc readInt* (self: TIniFile, sec, key: string, default: Int = 0): Int =
  parseOrDefault(self.readKey(sec, key), parseInt, default)

proc readBiggestInt* (self: TIniFile, sec, key: string, default: biggestInt = 0): biggestInt =
  parseOrDefault(self.readKey(sec, key), parseBiggestInt, default)

proc readFloat* (self: TIniFile, sec, key: string, default: Float = 0.0): Float =
  parseOrDefault(self.readKey(sec, key), parseFloat, default)

proc readEnum* [T: enum] (self: TIniFile, sec, key: string, default: T): T =
  parseOrDefault(self.readKey(sec, key), parseEnum[T], default)
  
proc readSection * (self: TIniFile, sec: string, withComments: bool = false): seq[string] =
  result = @[]
  let it = self.keys.find(sec.istring)
  if not isNil(it) :
    for line in self.sections[it.index].lines :
      if not isNil(line) and (withComments or not (line[0] in {';', '#'})) : result.add(line)
      
proc readSectionKeys * (self: TIniFile, sec: string): seq[string] =
  var res: seq[string] = @[]
  let it = self.keys.find(sec.istring)
  if not isNil(it) :
    self.sections[it.index].keys.forEachKey proc(k: istring) = res.add(k.string)
  return res

proc readSections * (self: TIniFile): seq[string] =
  result = @[]
  for sec in self.sections :
    result.add(sec.name)
        
proc forceSection(self: TIniFile, sec: string): int {.inline.} =
  #let sName = sec.tolower
  let it = self.keys.findOrInsert(sec)
  result = it.index
  if result < 0 :
    self.sections.add((name: sec, lines: @[], keys: nil))
    result = self.sections.high
    it.setIndex(result)

proc writeSection * (self: TIniFile, sec: string, data: openarray[string], preserveComments: Bool = false) =
  let idx = self.forceSection(sec)
  var finalComments : seq[string] = @[]
  if preserveComments :
    var isLeading = true
    var cntLeading = 0
    for line in self.sections[idx].lines:
      if line[0] == ';' or line[0] == '#' :
        if isLeading :
          inc(cntLeading)
        else :
          finalComments.add(line)
      else :
        isLeading = false
    self.sections[idx].lines.setLen(cntLeading)
  else :
    self.sections[idx].lines.setLen(0)
  self.sections[idx].keys = nil
  for line in data :
    self.keyAdd(line, idx)
  for line in finalComments : 
    self.sections[idx].lines.add(line)
     
proc hasSection* (self: TIniFile, sec: string): bool = not IsNil(self.keys.Find(sec.istring))

proc hasKey* (self: TIniFile, sec, key: string): bool =
  let it = self.keys.Find(sec.istring)
  return not isNil(it) and not isNil(self.sections[it.index].keys.Find(key.istring))

proc eraseKey* (self: TIniFile, sec, key: string): bool {.discardable.} =
  let it = self.keys.Find(sec.istring)
  if not isNil(it) :
    let idx = it.index
    let itk = self.sections[idx].keys.Find(key.istring)
    if not isNil(itk) : 
      self.sections[idx].lines[itk.value.x] = nil
      self.sections[idx].keys.Delete(itk.key)
      return true
  return false

proc eraseSection * (self: TIniFile, sec: string): bool {.discardable.} =
  let it = self.keys.DeleteSlot(sec)
  result = not isNil(it) 
  if result :
    var w = addr(self.sections[it.index])
    w[].name = nil
    w[].lines = nil
    w[].keys = nil

proc writeKey* (self: TIniFile, sec, key, value: string) =
  when false :
    if value == "" : self.eraseKey(sec, key)
    else : nil
    
  let idx = self.forceSection(sec)
  #let sKey = key.tolower
  let itk = self.sections[idx].keys.findOrInsert(key)
  if itk.value.delim == 0 :
    let sLine = repeatStr(self.space.indent, " ") & key & repeatStr(self.space.before, " ") & "=" &  repeatStr(self.space.after, " ") & value
    itk.value.delim = key.len + 1 + self.space.indent + self.space.before
    self.sections[idx].lines.add(sline)
    itk.value.x = self.sections[idx].lines.high
  else :
    self.sections[idx].lines[itk.value.x] = self.sections[idx].lines[itk.value.x].substr(0, itk.value.delim - 1) & repeatStr(self.space.after, " ") & value 

proc writeBool* (self: TIniFile, sec, key: string, value: Bool) =
  self.writeKey(sec, key, $value)

proc writeInt* (self: TIniFile, sec, key: string, value: Int) =
  self.writeKey(sec, key, $value)

proc writeBiggestInt* (self: TIniFile, sec, key: string, value: biggestInt) =
  self.writeKey(sec, key, $value)

proc writeFloat* (self: TIniFile, sec, key: string, value: Float) =
  self.writeKey(sec, key, $value)

proc writeEnum* [T: enum] (self: TIniFile, sec, key: string, value: T) =
  self.writeKey(sec, key, $value)
      

template exportImpl(self: TIniFile, onNewLine: expr): stmt {.immediate.} =
  for s in self.sections :
    if isNil(s.name) : continue
    onNewLine("[" & s.name & "]")
    for line in s.lines : 
      if line != nil : onNewLine(line)  
      
proc toString* (self: TIniFile, delim: string = "\n"): string =
  let lDelim = delim.len
  var total = 0
  for s in self.sections :
    total += s.name.len + 2 + lDelim
    for line in s.lines : 
      if line != nil : total += line.len + lDelim  
  result = newStringOfCap(total)
  template addNewLine(s) {.immediate.} = result &= s & delim 
  exportImpl(self, addNewLine)

proc updateFile * (self: TIniFile) =
  var f: TFile
  finally : 
    if f != stdout : close(f)
  if not isNil(self.fileName) and self.fileName != "" :
    f = open(self.fileName, fmWrite)
    
  else :
    f = stdout
  template addNewLine(s) {.immediate.} = writeln( f, s) 
  exportImpl(self, addNewLine ) 

iterator allSections* (self: TIniFile): string {.inline.} =
  for sec in self.sections : yield sec.name
    
iterator allKeys* (self: TIniFile, sec: string): string =
  let it = self.keys.find(sec.istring)
  if not isNil(it) :
    forLoop k, self.sections[it.index].keys.keys() :
      yield k.string
    
when isMainModule:
  import commandline
  
  var ini = """
 nix = is Gut
[Abc]    
 teSt = 123
 flag = on
 count = 23
    """.fromString.setFormat ((1,1,1))
  echo ini.readKey("abC", "test")
  echo ini.readKey("", "Nix")
  echo ini.readKey("nicht", "da", "stimmt")
  echo ini.eraseKey("abc", "test")
  echo ini.readKey("abC", "test", "bin mal weg")
  
  ini.writekey("abc", "test", "bin wieder da")
  echo ini.readKey("abC", "test", "bin mal weg")
  
  echo ini.toString
  echo ini.readBool("abc", "flag", false)
  echo ini.readInt("abc", "count", 0)  
  echo ini.readInt("abc", "x", 212)    
  echo ini.readInt("abc", "test", 213)
  
  ini.writeInt("abc", "x", 10212)    
  echo ini.readInt("abc", "x", 212)    
  echo ini.readSection("abc").repr
  ini.writeSection("abc", ["key=test", "another=true"])
  echo ini.readInt("abc", "x", 212)    
  echo ini.readKey("abc", "key", "ok")    
  echo ini.readSectionKeys("abc").repr
  
  var cl = ParseParams()
  
  if existsFile(cl.Data[0]) :
    ini = fromFile(cl.Data[0])
    for sec in ini.allSections :
      echo "[", sec, "]"
      for key in ini.allKeys(sec) :
        echo " ", key, " = ", ini.readKey(sec, key)
    echo ini.toString    
    
    