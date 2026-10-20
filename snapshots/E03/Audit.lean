import FailureOfSemipositiveMetricExtension.CentralQLocalSimple
import FailureOfSemipositiveMetricExtension.CentralQSubmersion
import Lean.Util.CollectAxioms

set_option pp.all true
set_option pp.universes true
set_option pp.maxSteps 1000000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Lean in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`FailureOfSemipositiveMetricExtension.CentralQLocalSimple, `FailureOfSemipositiveMetricExtension.CentralQSubmersion]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut names : Array Name := #[]
  let mut compilerOnly : Array Name := #[]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if modules.contains env.header.moduleNames[idx.toNat]! then
        if info.isUnsafe then
          compilerOnly := compilerOnly.push name
        else
          names := names.push name
  for name in compilerOnly.qsort Name.lt do
    let info := env.find? name |>.get!
    logInfo m!"COMPILER_ONLY {name} : {info.type}"
    logInfo m!"COMPILER_INSTANCE_STATUS {name}: {Lean.Meta.isInstanceCore env name}"
    let (_, state) := ((CollectAxioms.collect name).run env).run {}
    let mut missing : Array Name := #[]
    for dependency in state.visited do
      if (env.checked.get.find? dependency).isNone then
        missing := missing.push dependency
    logInfo m!"COMPILER_ONLY_UNRESOLVED_PRIMITIVES {name}: {missing.qsort Name.lt}"
    logInfo m!"COMPILER_ONLY_DIAGNOSTIC_AXIOMS {name}: {state.axioms.qsort Name.lt}"
  for name in names.qsort Name.lt do
    let info := env.find? name |>.get!
    logInfo m!"KERNEL_TYPE {name} : {info.type}"
    logInfo m!"INSTANCE_STATUS {name}: {Lean.Meta.isInstanceCore env name}"
    let (_, state) := ((CollectAxioms.collect name).run env).run {}
    for dependency in state.visited do
      if (env.checked.get.find? dependency).isNone then
        throwError "Missing dependency for {name}: {dependency}"
    let axioms := state.axioms
    let unexpected := axioms.filter (fun a => !allowed.contains a)
    if !unexpected.isEmpty then
      throwError "Unexpected axioms for {name}: {unexpected}"
    logInfo m!"KERNEL_DECL {name}: checked; axioms {axioms.qsort Name.lt}"
  logInfo m!"Q_TRANSVERSE_TWO_FULL_AUDIT_COMPLETE safe={names.size} compilerOnly={compilerOnly.size} modules={modules.size}"

