import Erdos708.H97.Audit
import Lean.Replay

open Lean Elab

/- Recheck all imported H97 declarations against their current definitions in a
fresh kernel environment containing only the existing external development.
This is an audit command; it creates no mathematical assumption or theorem. -/
run_elab do
  let env ← getEnv
  let mut constants : Std.HashMap Name ConstantInfo := {}
  let mut executableHelpers := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if (`Erdos708.H97).isPrefixOf env.header.moduleNames[idx.toNat]! then
        if info.isUnsafe || info.isPartial then
          executableHelpers := executableHelpers + 1
        if let .axiomInfo _ := info then
          throwError "Unexpected H97 axiom: {name}"
        constants := constants.insert name info
  let safeCount := constants.size - executableHelpers
  logInfo m!"Replaying {safeCount} H97 kernel declarations; {executableHelpers} compiler execution helpers excluded by Lean.Replay"
  let base ← liftM (m := IO) <| importModules #[{ module := `Mathlib },
    { module := `Erdos708.H17.Chain19.Results }] {} 0
  let checked ← liftM (m := IO) <| base.toKernelEnv.replay constants
  unless (checked.find? `Erdos708H97.hinge97).isSome &&
      (checked.find? `Erdos708H97.g_le_12n).isSome do
    throwError "Replay omitted a final theorem"
  logInfo m!"PASS: {safeCount} H97 declarations kernel-replayed, including hinge97 and g_le_12n"
