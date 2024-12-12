/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.CoreM
import Lean4Checker.Lean
import Lean.Data.HashMap
import Init.Data.String.Basic
import Lean.AddDecl

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

def functionNames : Array String := #["add", "sub", "neg", "abs", "mul", "udiv", "urem", "sdiv",
        "srem", "smod", "umod", "ofBool", "fill", "extract", "extractLsb\'",
        "zeroExtend", "shiftLeftZeroExtend", "zeroExtend\'", "signExtend",
        "and", "or", "xor", "not",  "shiftLeft", "ushiftRight", "sshiftRight",
        "sshiftRight\'", "rotateLeft", "rotateRight", "append", "replicate",
        "concat", "twoPow"]

def accessorNames := #["toNat", "toInt", "toFin", "getElem", "getLsbD", "getMsbD", "msb"]

open Lean in
/-- Draw the hashmap as a latex table. -/
def renderCSVTable (t : Std.HashSet (String × String) ) : String := Id.run do
  let mut out := "accessor,function,doesExist\n"
  for fn in functionNames do
    for acc in accessorNames do
      out := out ++ s!"{acc},{fn},{t.contains (acc, fn)}" ++ "\n"
  return out

/-- O(n^2) substring search, where we check if 'pat' occurs in 's'. -/
partial def _root_.String.containsSubstr? (s pat : String) : Bool :=
  -- empty string is subtring of itself.
  if s.length == 0 then
    pat.length == 0
  else
    if pat.isPrefixOf s
    then True
    else (s.drop 1).containsSubstr? pat

open Lean in
unsafe def replay (module : Name) : IO Unit := do
  diffEnvironments module fun before after => do
    -- please give me all the things that were added.
    let newConstants := after.constants.map₁.toList.filter
      -- We skip unsafe constants, and also partial constants. Later we may want to handle partial constants.
      fun ⟨n, ci⟩ => !before.constants.map₁.contains n && !ci.isUnsafe && !ci.isPartial

    let mut table : Std.HashSet (String × String) := ∅

    for (constName, constInfo) in newConstants do
      IO.println "--"
      IO.println constName
      if let .thmInfo info := constInfo then
        for acc in accessorNames do
          for fn in functionNames do
            let haveThm? := constName.toString.containsSubstr? acc && constName.toString.containsSubstr? fn
            if haveThm? then 
              table := table.insert (acc, fn)
              IO.println s!"* {constName} is a theorem, with value '{info.value.hash}'"

    IO.FS.writeFile "theorem-table.csv" (renderCSVTable table)
    IO.println (renderCSVTable table)

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
