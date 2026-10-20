import FailureOfSemipositiveMetricExtension.HisamotoLocalExtensionEndpoint
import Lean.Util.CollectAxioms
set_option pp.maxSteps 1000000
open Lean in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`FailureOfSemipositiveMetricExtension.HisamotoIncidence,
    `FailureOfSemipositiveMetricExtension.HisamotoLocalTopology,
    `FailureOfSemipositiveMetricExtension.HisamotoManifold,
    `FailureOfSemipositiveMetricExtension.HisamotoLineBundle,
    `FailureOfSemipositiveMetricExtension.HisamotoExceptionalDivisor,
    `FailureOfSemipositiveMetricExtension.BlowupManifold,
    `FailureOfSemipositiveMetricExtension.HisamotoBlowupComparison,
    `FailureOfSemipositiveMetricExtension.HisamotoNormalQuotient,
    `FailureOfSemipositiveMetricExtension.HisamotoNormalBundle,
    `FailureOfSemipositiveMetricExtension.HisamotoBundleIsomorphism,
    `FailureOfSemipositiveMetricExtension.HisamotoMetricPullback,
    `FailureOfSemipositiveMetricExtension.HisamotoFibreGeometry,
    `FailureOfSemipositiveMetricExtension.HisamotoBlowdownComplement,
    `FailureOfSemipositiveMetricExtension.HisamotoStrictTransform,
    `FailureOfSemipositiveMetricExtension.HisamotoCompactSurface,
    `FailureOfSemipositiveMetricExtension.HisamotoTensorBundle,
    `FailureOfSemipositiveMetricExtension.HisamotoTensorIsomorphism,
    `FailureOfSemipositiveMetricExtension.HisamotoHyperplaneBundle,
    `FailureOfSemipositiveMetricExtension.HisamotoExceptionalSection,
    `FailureOfSemipositiveMetricExtension.HisamotoLocalExtensionEndpoint]
  let mut names : Array Name := #[]
  let mut excluded : Nat := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if modules.contains env.header.moduleNames[idx.toNat]! then
        if info.isUnsafe then
          excluded := excluded + 1
          logInfo m!"COMPILER_ONLY_UNSAFE {name}"
        else
          names := names.push name
  for name in names.qsort Name.lt do
    let axioms ← collectAxioms name
    let unexpected := axioms.filter (fun a => a != ``propext && a != ``Classical.choice && a != ``Quot.sound)
    if !unexpected.isEmpty then
      throwError "Unexpected axioms for {name}: {unexpected}"
    logInfo m!"AXIOMS {name}: {axioms.qsort Name.lt}"
  logInfo m!"AUDIT SUMMARY: {names.size} safe kernel declarations audited by actual ownership; {excluded} compiler-only unsafe helpers separately counted."
