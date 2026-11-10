import PredictionDepth
import Lean.Elab.Command

/-! Report the same import metadata used to select declarations in `Audit.lean`. -/

open Lean Elab Command in
run_elab do
  for name in (← getEnv).allImportedModuleNames do
    IO.println name
