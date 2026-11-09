import PredictionDepth
import Lean.Util.CollectAxioms

/-! Fail the audit if any project declaration transitively uses an unapproved
axiom, including `sorryAx`. Select declarations by their defining module so
generated declarations and declarations in other namespaces are included. -/
open Lean Elab Command in
run_elab do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let names := env.constants.fold (init := #[]) fun names n _ =>
    if (env.getModuleIdxFor? n).any (fun idx => (`PredictionDepth).isPrefixOf modules[idx.toNat]!) then
      names.push n
    else names
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in names do
    for ax in (← collectAxioms n) do
      unless allowed.contains ax do
        throwError "{n} transitively depends on unapproved axiom {ax}"
  logInfo m!"Audited {names.size} project declarations: only propext, Classical.choice, Quot.sound."
