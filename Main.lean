/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.CoreM
import Lean4Checker.Lean
-- import Std.Data.HashMap
import Lean.Data.HashMap
import Init.Data.String.Basic
import Lean.AddDecl
-- import System.FilePath

open Lean

structure Context where
  -- new constants or whatever.
  newConstants : HashMap Name ConstantInfo

structure State where
  /-- A Lean environment, which has declarations, theorems, and stuff.-/
  env : Environment
  -- some kind of BFS
  remaining : NameSet := {}
  pending : NameSet := {}

-- our monad, helpfully named m.
abbrev M := ReaderT Context <| StateT State IO

-- function to run said monad.
def M.run (env : Environment) (newConstants : HashMap Name ConstantInfo) (act : M α) : IO α :=
  StateT.run' (s := { env, remaining := newConstants.keyNameSet }) do
    ReaderT.run (r := { newConstants }) do
      act


/-- Check if a `Name` still needs processing. If so, move it from `remaining` to `pending`. -/
def isTodo (name : Name) : M Bool := do
  let r := (← get).remaining
  if r.contains name then
    modify fun s => { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
    return true
  else
    return false

/-- Use the current `Environment` to throw a `KernelException`. -/
def throwKernelException (ex : KernelException) : M Unit := do
    let ctx := { fileName := "", options := ({} : KVMap), fileMap := default }
    let state := { env := (← get).env }
    Prod.fst <$> (Lean.Core.CoreM.toIO · ctx state) do Lean.throwKernelException ex

/-
def addDecl (d : Declaration) : M Unit := do
  let s ← get
  match Lean.Environment.addDecl s.env Lean.Options. d with
  | .ok env' =>
    modify fun s => { s with env := env' : State }
  | .error ex =>
    throwKernelException ex
-/
/-
mutual
/--
Check if a `Name` still needs to be processed (i.e. is in `remaining`).

If so, recursively replay any constants it refers to,
to ensure we add declarations in the right order.

The construct the `Declaration` from its stored `ConstantInfo`,
and add it to the environment.
-/
partial def replayConstant (name : Name) : M Unit := do
  if ← isTodo name then
    let some ci := (← read).newConstants.find? name | unreachable!
    replayConstants ci.getUsedConstants
    -- Check that this name is still pending: a mutual block may have taken care of it.
    if (← get).pending.contains name then
      match ci with
      | .defnInfo   info =>
        IO.println s!"Replaying defn {name}"
        -- addDecl (Declaration.defnDecl   info)
      | .thmInfo    info =>
        -- Add code here to check what theorem we have or whatever.
        IO.println s!"Replaying thm {name}"
        -- check if name contains toInt, and if so, record that we have toInt lemma.
        -- addDecl (Declaration.thmDecl    info)
      | .axiomInfo  info =>
        IO.println s!"Replaying axiom {name}"
        -- addDecl (Declaration.axiomDecl  info)
      | .opaqueInfo info =>
        IO.println s!"Replaying opaque {name}"
        -- addDecl (Declaration.opaqueDecl info)
      | .inductInfo info =>
        IO.println s!"Replaying inductive {name}"
        let lparams := info.levelParams
        let nparams := info.numParams
        let all ← info.all.mapM fun n => do pure <| ((← read).newConstants.find! n)
        for o in all do
          modify fun s =>
            { s with remaining := s.remaining.erase o.name, pending := s.pending.erase o.name }
        let ctorInfo ← all.mapM fun ci => do
          pure (ci, ← ci.inductiveVal!.ctors.mapM fun n => do
            pure ((← read).newConstants.find! n))
        -- Make sure we are really finished with the constructors.
        for (_, ctors) in ctorInfo do
          for ctor in ctors do
            replayConstants ctor.getUsedConstants
        let types : List InductiveType := ctorInfo.map fun ⟨ci, ctors⟩ =>
          { name := ci.name
            type := ci.type
            ctors := ctors.map fun ci => { name := ci.name, type := ci.type } }
        -- addDecl (Declaration.inductDecl lparams nparams types false)
      -- We discard `ctorInfo` and `recInfo` constants. These are added when generating inductives.
      | .ctorInfo _ =>
        IO.println s!"Skipping constructor {name}"
      | .recInfo _ =>
        IO.println s!"Skipping recursor {name}"
      | .quotInfo _ =>
        IO.println s!"Replaying quotient {name}"
        -- addDecl (Declaration.quotDecl)
      modify fun s => { s with pending := s.pending.erase name }

/-- Replay a set of constants one at a time. -/
partial def replayConstants (names : NameSet) : M Unit := do
  for n in names do replayConstant n

end
-/

/--
Given a module, obtain the environments
* `before`, by importing all its imports but not processing the contents of the module
* `after`, by importing the module
and then run a function `act before after`.
-/
unsafe def diffEnvironments (module : Name) (act : Environment → Environment → IO α) : IO α := do
  Lean.withImportModules #[{module}] {} 0 fun after => do
    Lean.withImportModules (after.importsOf module) {} 0 fun before =>
      act before after

def accessorNames : Array String := #[
    "toInt",
    "toNat"
 ]

def functionNames : Array String := #[
  "signExtend",
  "add",
  "sub"
]


open Lean in
/-- Draw the hashmap as a latex table. -/
def renderLatexTable (t : HashMap (String × String) Bool) : String := Id.run do
  let mut out := ""
  let numRows := functionNames.size
  out := out.append "\\begin{tabular}"
  for fn in functionNames do
    for acc in accessorNames do
      pure ()
  out := out.append "\\end{tabular}"
  return out

/--
Pad a string to the right to ensure that it uses at least 'amt' space.
will not pad if length exceeds 'amt'.
-/
def padRight (s : String) (amt : Nat) : String :=
  String.pushn s ' ' (amt - s.length)

/--
Pad a string to the left to ensure that it uses at least 'amt' space.
will not pad if length exceeds 'amt'.
-/
def padLeft (s : String) (amt : Nat) : String :=
  let padding := "".pushn ' ' (amt - s.length)
  padding ++ s

/-- Draw the hashmap as a latex table. -/
def renderMarkdownTable (t : HashMap (String × String) Bool) : String := Id.run do
  let mut out := ""

  let accessorPad := accessorNames.foldl (init := 0) fun n acc => Nat.max n acc.length + 2
  let fnPad := functionNames.foldl (init := 0) fun acc fn => Nat.max acc fn.length + 2
  let pad := Nat.max fnPad accessorPad

  for fn in #[""] ++ functionNames do
    out := out.append "|"
    out := out.append <| padRight fn pad

  for acc in accessorNames do
    out := out.append "\n"
    out := out.append "|"
    out := out.append <| padRight acc pad

    for fn in functionNames do
      if t.contains (acc, fn) then
        out := out.append "|"
        out := out.append <| padRight "\\tableok" pad
      else
        out := out.append "|"
        out := out.append <| padRight "\\tableno" pad
  return out


partial def _root_.String.containsSubstr? (needle : String) (haystack: String) : Bool :=
  -- empty string is subtring of itself.
  if haystack.length == 0 then needle.length == 0
  else
    if haystack.isPrefixOf needle
    then True
    else containsSubstr? needle (haystack.drop 1)

-- Z-algorithm for string substring matching
-- Actually linear time, actually easy to implement! Unlike the weirder ones.
-- Competitive programming reference: https://cp-algorithms.com/string/z-function.html
-- Good algorithmic references: Algorithms on Strings, Sequences, and Trees [Good explanation]
-- Sexy algorithmic reference: Jewels of Stringology (Kawaii explanation, not very sensible on first read).
def containsSubstr₂ (needle haystack : String) : Bool :=
  Id.run do
    let n := haystack.length
    let mut z : Array Nat := Array.mkEmpty n
    let mut pos : Nat := 0
    let mut l : Nat := 0
    let mut r : Nat := 0
    for _ in [1:haystack.length] do
      if pos < r then
        z := z.push (min (r - pos) (z.get! (pos - l)))
      let p1 : String.Pos := {byteIdx := z.get! pos}
      let p2 : String.Pos := {byteIdx := pos + z.get! pos}
      while (pos + z.get! pos < n && needle.get! p1 == haystack.get! p2) do
          z := z.set! pos (z.get! pos + 1)

      if (r < pos + z.get! pos) then
        l := pos
        r := pos + z.get! pos
      pos := pos + 1
    for zz in z do
        if zz = needle.length then
          return True
    return False

open Lean in
unsafe def replay (module : Name) : IO Unit := do
  diffEnvironments module fun before after => do
    -- please give me all the things that were added.
    let newConstants := after.constants.map₁.toList.filter
      -- We skip unsafe constants, and also partial constants. Later we may want to handle partial constants.
      fun ⟨n, ci⟩ => !before.constants.map₁.contains n && !ci.isUnsafe && !ci.isPartial

    let mut table : HashMap (String × String) Bool := HashMap.empty

    for (constName, constInfo) in newConstants do
      -- do our filtering / tabulating / ...
      IO.println constName
      if let .thmInfo info := constInfo then
        for acc in accessorNames do
          for fn in functionNames do
            let haveThm? := constName.toString.containsSubstr? acc && constName.toString.containsSubstr? fn
            table := table.insert (acc, fn) haveThm?
        IO.println s!"* {constName} is a theorem, with value '{info.value.hash}'"

    IO.FS.writeFile "table.tex" (renderLatexTable table)

    IO.println "---"
    IO.println (renderMarkdownTable table)

/--
Run as e.g. `lake exe lean4checker Mathlib.Data.Nat.Basic`.

This will replay all the new declarations from this file into the `Environment`
as it was at the beginning of the file, using the kernel to check them.

This is not an external verifier, simply a tool to detect "environment hacking".
-/
unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let module ← match args with
    | [mod] => match Syntax.decodeNameLit s!"`{mod}" with
      | some m => pure m
      | none => throw <| IO.userError s!"Could not resolve module: {mod}"
    | _ => throw <| IO.userError "Usage: lake exe lean4checker Mathlib.Data.Nat.Basic"
  replay module
  return 0
