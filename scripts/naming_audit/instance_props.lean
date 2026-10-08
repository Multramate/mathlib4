import Mathlib

/-!
Dump every instance declared in Mathlib as `name<TAB>prop|data`, and every `Has…` name as
`name<TAB>has`, so that
`naming_audit.py --instance-props FILE` can tell `Prop`-valued instances (whose snake_case names
are conventional) from data instances (whose names should be lowerCamelCase or absent).

Run from a built Mathlib checkout: `lake env lean scripts/naming_audit/instance_props.lean > FILE`.
-/

open Lean Meta Elab Command in
run_cmd do
  let env ← getEnv
  let insts := (Meta.instanceExtension.getState env).instanceNames
  let mut out := #[]
  for (n, _) in insts do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`Mathlib).isPrefixOf mod do continue
    let some ci := env.find? n | continue
    let isProp ← liftTermElabM <| Meta.isProp ci.type
    out := out.push s!"{n}\t{if isProp then "prop" else "data"}"
  -- Every `Has…` name in the environment, including those `to_dual`/`to_additive` generate and the
  -- source never spells out (`HasColimits`, `HasCoequalizers`), so that `hasColimits` is not taken for
  -- a Lean 3 `has_…` relic.
  for (n, _) in env.constants.toList do
    if let .str _ s := n then
      if s.startsWith "Has" then
        out := out.push s!"{n}\thas"
  IO.println (String.intercalate "\n" out.qsort.toList)
