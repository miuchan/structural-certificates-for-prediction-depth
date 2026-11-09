import PredictionDepth
import Lean.Util.CollectAxioms

/-! Fail the build if any project declaration transitively uses an unapproved
axiom, including `sorryAx`. The usual Lean logical axioms are listed explicitly.
This checks declarations, not textual appearances of proof placeholders. -/
open Lean Elab Command in
run_elab do
  let names ← (← getEnv).constants.foldM (init := #[]) fun names n _ => do
    let userName := (privateToUserName? n).getD n
    if (`PredictionDepth).isPrefixOf userName then
      pure (names.push n)
    else pure names
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in names do
    for ax in (← collectAxioms n) do
      unless allowed.contains ax do
        throwError "{n} transitively depends on unapproved axiom {ax}"
  logInfo m!"Audited {names.size} project declarations: only propext, Classical.choice, Quot.sound."
