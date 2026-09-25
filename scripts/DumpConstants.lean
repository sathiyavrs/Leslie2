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

A type and a value name the constants they mention, so a hash changes whenever
a constant the declaration mentions is renamed. An optional argument takes a
two-column file of `old<TAB>new` names, the one
`scripts/check-constant-drift.py` reads, and every new name it holds is written
back to its old one, prefix-wise, before the type and the value are hashed. A
fingerprint then says what a rename must leave alone, and the columns the
reference is compared against stay in the reference's own vocabulary.

`scripts/check-constant-drift.py` compares two such fingerprints. Run this
script from the repository root::

    lake env lean --run scripts/DumpConstants.lean
    lake env lean --run scripts/DumpConstants.lean renames.tsv
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
    isNumbered "eq_" s || isNumbered "_eq_" s || isNumbered "_sparseCasesOn_" s

/-- Whether any component of `n` marks an auxiliary constant. -/
def hasAuxiliaryComponent : Name → Bool
  | .anonymous => false
  | .num p _ => hasAuxiliaryComponent p
  | .str p s => isAuxiliaryComponent s || hasAuxiliaryComponent p

/-- Whether the fingerprint omits `n`. -/
def isAuxiliary (env : Environment) (n : Name) : Bool :=
  hasAuxiliaryComponent n || isAuxRecursor env n || isRecCore env n ||
    isMatcherCore env n || isCasesOnRecursor env n || isNoConfusion env n

/-- `s` without its leading and trailing blanks. -/
def trimmed (s : String) : String :=
  let blank (c : Char) : Bool := c == ' ' || c == '\t' || c == '\r' || c == '\n'
  String.ofList ((s.toList.dropWhile blank).reverse.dropWhile blank).reverse

/-- A two-column file of `old<TAB>new` names, read as new to old and ordered
with the longest new name first, so that a prefix match is the longest one. -/
def readRenames (path : System.FilePath) : IO (Array (Name × Name)) := do
  let mut out : Array (Name × Name) := #[]
  for line in (← IO.FS.readFile path).splitOn "\n" do
    let line := trimmed ((line.splitOn "#").headD line)
    if line.isEmpty then
      continue
    match line.splitOn "\t" with
    | [old, new] => out := out.push ((trimmed new).toName, (trimmed old).toName)
    | _ => throw (IO.userError s!"a rename row is not two columns: {line}")
  return out.qsort fun a b => a.1.toString.length > b.1.toString.length

/-- The old name of `n` under `renames`, taken at the longest new name that is
a prefix of it, so that an auxiliary constant follows the declaration it
belongs to. -/
def unrename (renames : Array (Name × Name)) (n : Name) : Name := Id.run do
  for (new, old) in renames do
    if new.isPrefixOf n then
      return (old.toString ++ (n.toString.drop new.toString.length)).toName
  return n

/-- `e` with every renamed constant taken back to its old name, in the constants it
mentions and in the structure names its projection nodes carry. -/
partial def unrenameExpr (renames : Array (Name × Name)) (e : Expr) : Expr :=
  if renames.isEmpty then e else
    e.replace fun s => match s with
      | .const n us =>
        let m := unrename renames n
        if m == n then none else some (.const m us)
      | .proj n i b =>
        let m := unrename renames n
        if m == n then none else some (.proj m i (unrenameExpr renames b))
      | _ => none

/-- The canonical universe parameters `u_0, u_1, …`, one for each parameter of `levelParams`. -/
def canonicalLevels (levelParams : List Name) : List Level :=
  (List.range levelParams.length).map fun i => .param (Name.mkSimple s!"u_{i}")

/-- The hash of `e`, taken with the universe parameters instantiated
canonically and every renamed constant taken back to its old name. -/
def shapeHash (renames : Array (Name × Name)) (levelParams : List Name) (e : Expr) : UInt64 :=
  (unrenameExpr renames (e.instantiateLevelParams levelParams (canonicalLevels levelParams))).hash

/-- The module that holds `n`, or `?` for a constant the environment attributes to none. -/
def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => `«?»

/-- The row for one constant, tab-separated. -/
def row (renames : Array (Name × Name)) (env : Environment) (n : Name)
    (info : ConstantInfo) : MetaM (String × String) := do
  let userName := (privateToUserName? n).getD n
  let levels := info.levelParams
  let typeHash := shapeHash renames levels info.type
  let valueHash := match info.value? with
    | some v => toString (shapeHash renames levels v)
    | none => "-"
  let isSimp := (← getSimpTheorems).isLemma (.decl n)
  let isInst ← Meta.isInstance n
  let columns := [toString userName, toString (moduleOf env n), toString levels.length,
    toString typeHash, valueHash, if isSimp then "simp" else "-", if isInst then "inst" else "-"]
  return (toString userName, String.intercalate "\t" columns)

/-- The rows for every constant of the library, sorted by user-facing name. -/
def rows (renames : Array (Name × Name)) : MetaM (Array String) := do
  let env ← getEnv
  let mut out : Array (String × String) := #[]
  for (n, info) in env.constants.toList do
    unless (moduleOf env n) == library || library.isPrefixOf (moduleOf env n) do
      continue
    if isAuxiliary env n then
      continue
    out := out.push (← row renames env n info)
  let sorted := out.qsort fun a b => a.1 < b.1
  return sorted.map Prod.snd

end DumpConstants

def main (args : List String) : IO Unit := do
  let renames ← match args with
    | [] => pure #[]
    | [path] => DumpConstants.readRenames path
    | _ => throw (IO.userError "usage: DumpConstants.lean [renames.tsv]")
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := DumpConstants.library }] {} (trustLevel := 1024)
  let context : Core.Context :=
    { fileName := "DumpConstants.lean", fileMap := default, maxHeartbeats := 0 }
  let state : Core.State := { env }
  let (out, _) ← ((DumpConstants.rows renames).run').toIO context state
  let stdout ← IO.getStdout
  stdout.putStr (String.intercalate "\n" out.toList)
  stdout.putStr "\n"
