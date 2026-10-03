import GraphicalAllocation
import Lean

/-! Collect transitive kernel axioms for every imported project declaration. -/

open Lean in
run_elab do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut used : Array Name := #[]
  for (name, info) in env.constants.toList do
    let text := name.toString
    if text.startsWith "GraphicalAllocation." || text.startsWith "_private.GraphicalAllocation." then
      declarations := declarations + 1
      if info.isTheorem then
        theorems := theorems + 1
      if info.isUnsafe then
        throwError "Unsafe project declaration: {name}"
      let axioms ← Lean.collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
        unless used.contains axiomName do
          used := used.push axiomName
  logInfo m!"Kernel axiom audit passed: {declarations} project declarations, {theorems} theorems"
  logInfo m!"Axioms used: {used}"
