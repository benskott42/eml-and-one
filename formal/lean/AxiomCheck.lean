/-
  Automatic axiom audit for EVERY declaration in every `Eml.*` module.
  Run with `lake env lean AxiomCheck.lean` (enforced in CI):
  walks all declarations defined in `Eml` / `Eml.*` modules in a single shared
  `CollectAxioms.State` and fails compilation if ANY of them depends on an axiom
  outside Lean's standard three `[propext, Classical.choice, Quot.sound]`
  (catching `sorryAx`, custom axioms, and `Lean.ofReduceBool` / `native_decide`).
-/
import Lean
import Eml

open Lean

private def allowedAxioms : List Name :=
  [`propext, `Classical.choice, `Quot.sound]

#eval show CoreM Unit from do
  let env ← getEnv
  let mut checked := 0
  let mut state : CollectAxioms.State := {}
  let mut customAxioms : Array Name := #[]
  for i in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[i]!
    if modName == `Eml || modName.getRoot == `Eml then
      let mdata := env.header.moduleData[i]!
      for name in mdata.constNames do
        if name.isInternal then continue
        match env.find? name with
        | some (.thmInfo _) | some (.defnInfo _) =>
          let (_, s') := (CollectAxioms.collect name).run env state
          state := s'
          checked := checked + 1
        | some (.axiomInfo _) =>
          customAxioms := customAxioms.push name
        | _ => pure ()
  let bad := state.axioms.toList.filter (fun ax => !allowedAxioms.contains ax)
  if !customAxioms.isEmpty then
    throwError "Custom axiom(s) declared inside Eml.*: {customAxioms.toList}"
  if !bad.isEmpty then
    throwError "Disallowed axiom(s) used by Eml.* declarations: {bad}"
  if checked < 150 then
    throwError "Axiom audit checked unexpectedly few declarations ({checked}); check Eml import."
  IO.println s!"AxiomCheck OK: audited {checked} declarations across Eml.* modules; axioms = {state.axioms.toList}"
