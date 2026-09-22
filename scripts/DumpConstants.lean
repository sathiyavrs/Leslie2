/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols
import Lean

/-!
# A fingerprint of every constant of `Leslie2Protocols`

Splitting a file moves declarations between modules. The fingerprint this
script writes says what a move must leave alone: the constant's user-facing
name, the shape of its type, the shape of its value, and its simp and instance
status. The module is written too, and it is the one column a move is allowed
to change.

One tab-separated row per constant whose module sits in `Leslie2Protocols`,
sorted by name:

1. the user-facing name, so that a private declaration prints under the name a
   reader writes rather than under its mangled form;
2. the module that holds it;
3. the number of universe parameters;
4. the hash of the type, taken after the universe parameters are instantiated
   to `u_0, u_1, …` in order, so that renaming a universe parameter does not
   register as a change;
5. the hash of the value of a definition, taken the same way, and `-` for every
   other constant: a theorem is pinned by its statement, and an axiom, an
   inductive type, a constructor and a recursor carry no value at all;
6. `simp` when the constant is a lemma of the default simp set, `-` otherwise;
7. `inst` when the constant is an instance, `-` otherwise.

Auxiliary constants -- equation lemmas, matchers, recursors the kernel
generates, the compiler's stages -- are omitted: they are artefacts of the
declarations that carry them, and the declarations are already covered.

`scripts/check-constant-drift.py` compares two such fingerprints. Run this
script from the repository root::

    lake env lean --run scripts/DumpConstants.lean
-/

open Lean Meta

namespace DumpConstants

/-- The library whose constants the fingerprint covers. -/
def library : Name := `Leslie2Protocols

/-- Whether `s` is `start` followed by a nonempty run of digits, as `proof_3`. -/
def isNumbered (start : String) (s : String) : Bool :=
  s.startsWith start &&
    let rest := s.drop start.length
    !rest.isEmpty && rest.all Char.isDigit

/-- Whether a name component marks an auxiliary constant. -/
def isAuxiliaryComponent (s : String) : Bool :=
  s == "_auxLemma" || s == "_cstage1" || s == "_cstage2" || s == "_sunfold" ||
    s == "_unsafe_rec" || isNumbered "proof_" s || isNumbered "match_" s ||
    isNumbered "eq_" s || isNumbered "_eq_" s

/-- Whether any component of `n` marks an auxiliary constant. -/
def hasAuxiliaryComponent : Name → Bool
  | .anonymous => false
  | .num p _ => hasAuxiliaryComponent p
  | .str p s => isAuxiliaryComponent s || hasAuxiliaryComponent p

/-- Whether the fingerprint omits `n`. -/
def isAuxiliary (env : Environment) (n : Name) : Bool :=
  hasAuxiliaryComponent n || isAuxRecursor env n || isRecCore env n ||
    isMatcherCore env n || isCasesOnRecursor env n || isNoConfusion env n

/-- The canonical universe parameters `u_0, u_1, …`, one for each parameter of `levelParams`. -/
def canonicalLevels (levelParams : List Name) : List Level :=
  (List.range levelParams.length).map fun i => .param (Name.mkSimple s!"u_{i}")

/-- The hash of `e`, taken with the universe parameters instantiated canonically. -/
def shapeHash (levelParams : List Name) (e : Expr) : UInt64 :=
  (e.instantiateLevelParams levelParams (canonicalLevels levelParams)).hash

/-- The module that holds `n`, or `?` for a constant the environment attributes to none. -/
def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => `«?»

/-- The row for one constant, tab-separated. -/
def row (env : Environment) (n : Name) (info : ConstantInfo) : MetaM (String × String) := do
  let userName := (privateToUserName? n).getD n
  let levels := info.levelParams
  let typeHash := shapeHash levels info.type
  let valueHash := match info.value? with
    | some v => toString (shapeHash levels v)
    | none => "-"
  let isSimp := (← getSimpTheorems).isLemma (.decl n)
  let isInst ← Meta.isInstance n
  let columns := [toString userName, toString (moduleOf env n), toString levels.length,
    toString typeHash, valueHash, if isSimp then "simp" else "-", if isInst then "inst" else "-"]
  return (toString userName, String.intercalate "\t" columns)

/-- The rows for every constant of the library, sorted by user-facing name. -/
def rows : MetaM (Array String) := do
  let env ← getEnv
  let mut out : Array (String × String) := #[]
  for (n, info) in env.constants.toList do
    unless (moduleOf env n) == library || library.isPrefixOf (moduleOf env n) do
      continue
    if isAuxiliary env n then
      continue
    out := out.push (← row env n info)
  let sorted := out.qsort fun a b => a.1 < b.1
  return sorted.map Prod.snd

end DumpConstants

def main : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := DumpConstants.library }] {} (trustLevel := 1024)
  let context : Core.Context :=
    { fileName := "DumpConstants.lean", fileMap := default, maxHeartbeats := 0 }
  let state : Core.State := { env }
  let (out, _) ← (DumpConstants.rows.run').toIO context state
  let stdout ← IO.getStdout
  stdout.putStr (String.intercalate "\n" out.toList)
  stdout.putStr "\n"
