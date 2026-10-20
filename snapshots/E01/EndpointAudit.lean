import FailureOfSemipositiveMetricExtension

set_option pp.universes true
set_option pp.fullNames true

open FailureOfSemipositiveMetricExtension FailureOfSemipositiveMetricExtension.GlobalIncidence
open scoped Manifold ContDiff

-- Each instance is synthesized on the actual objects, without local hypotheses.
#synth T2Space Total
#synth SecondCountableTopology Total
#synth IsManifold 𝓘(ℂ,ChartCoord) ω Total
#synth T2Space (Fiber 0)
#synth SecondCountableTopology (Fiber 0)
#synth CompactSpace (Fiber 0)
#synth IsManifold 𝓘(ℂ,FixedFiber.Coord) ω (Fiber 0)
#synth CaoAdapter.powerCore.IsContMDiff 𝓘(ℂ,ChartCoord) ω

#check @GlobalLineBundle.no_semipositive_metric_dominating_centralH0
#check @GlobalLineBundle.no_exact_semipositive_extension
#check @GlobalLineBundle.no_semipositive_extension_same_local_singularity_type
#check @GlobalLineBundle.prescribed_semipositive_metric_nonextension
#check @GlobalLineBundle.SingularWeightOn.centralLocallyDominatesH0_of_local_frames
#check @GlobalLineBundle.SingularWeightOn.centralLocallyDominatesH0_dominates
#check @Literature.cao_extension_via_projective_immersion_psh_translation
#check @CaoExtensionInterface.ExtensionStatement
#check @CaoExtensionInterface.AdaptedFamily.mk
#check @CaoExtensionInterface.ProjectiveImmersion.mk
#check @CaoExtensionInterface.AnalyticLineBundle.mk
#check @CaoExtensionInterface.SemipositiveWeightOn.mk
#check @CaoExtensionInterface.CentralAdjointSection.mk
#check @CaoExtensionInterface.TotalAdjointSection.mk
#check @CaoExtensionInterface.RestrictionWellDefined
#check @CaoExtensionInterface.InRestrictedMultiplier
#check @CaoExtensionInterface.RestrictsByDt

#print axioms GlobalLineBundle.no_semipositive_metric_dominating_centralH0
#print axioms GlobalLineBundle.no_exact_semipositive_extension
#print axioms GlobalLineBundle.no_semipositive_extension_same_local_singularity_type
#print axioms GlobalLineBundle.prescribed_semipositive_metric_nonextension
#print axioms GlobalLineBundle.SingularWeightOn.centralLocallyDominatesH0_of_local_frames
#print axioms GlobalLineBundle.SingularWeightOn.centralLocallyDominatesH0_dominates
#print axioms CaoAdapter.family
#print axioms CaoAdapter.immersion
#print axioms CaoAdapter.fourthPowerLine
#print axioms CaoAdapter.fourthPowerWeight
#print axioms CaoAdapter.fourthPowerWeight_wellDefined
#print axioms CaoAdapter.sigmaCentralSection
#print axioms CaoAdapter.sigmaCentralSection_inRestrictedMultiplier
#print axioms CaoAdapter.sigmaCentralSection_no_extension
#print axioms FixedFiberBundle.sigma_global_norm_finite
#print axioms FixedFiberBundle.sigma_compared_global_norm_finite

#check @FixedFiberBundle.centralH0_hasMinimalSingularities
#check @FixedFiberBundle.halfDivisorResidual_exists
#check @FixedFiberBundle.centralH0_current_lelong_half
#check @FixedFiberBundle.centralH0_curvatureCurrent
#check @FixedFiberBundle.first_nonzero_central_integrable_adjoint_exponent
#check @FixedFiberBundle.actual_central_small_integrable_adjoint_section_zero
#check @FixedFiberBundle.CurveNormal.degreeHomeomorph
#check @FixedFiberBundle.CurveNormal.degreeHomeomorph_contMDiff
#check @FixedFiberBundle.CurveNormal.degreeHomeomorph_symm_contMDiff
#print FixedFiberBundle.HasMinimalSingularities
#print FixedFiberBundle.NonzeroCentralIntegrableAdjointSystem
#print PshCurvatureCurrentInterface.CurvatureCurrent
#print PshCurvatureCurrentInterface.HasLelongNumber
#print NegativeCurveRemovalInterface.RemovalStatement
#print PshCurvatureCurrentInterface.PshCurrentStatement
#print axioms FixedFiberBundle.centralH0_hasMinimalSingularities
#print axioms FixedFiberBundle.centralH0_current_lelong_half
#print axioms FixedFiberBundle.first_nonzero_central_integrable_adjoint_exponent
#print axioms FixedFiberBundle.CurveNormal.degreeHomeomorph
#print axioms QuadraticCurrentRegression.polarizedMixed_eq_neg_I

#check @GeneralCao.adjoint_obstruction
#check @GeneralCao.prescribed_metric_adjoint_extension_all_m
#check @GeneralCao.prescribed_metric_tensor_adjoint_extension_all_m
#check @GeneralCao.AnalyticLine.tensorBundleHomeomorph
#check @GeneralCao.AnalyticLine.tensorBundleHomeomorph_analytic
#check @GeneralCao.multiplier_germs_finite_canonical_norm
#print GeneralCao.Family
#print GeneralCao.SemipositiveWeight
#print GeneralKahler.KahlerForm
#print GeneralCao.TensorCentralAdjointSection
#print GeneralCao.TensorTotalAdjointSection
#print GeneralCao.TensorRestrictsByDt
#print Literature.cao_extension_proper_disc_kahler_psh_translation
#check @RelativeSegre.incidenceFunctorPoint
#check @RelativeSegre.incidenceFunctorPoint_projection
#check @RelativeSegre.complexPointEquiv
#check @BlowdownComplement.localizedIncidenceOpenIso
#synth AlgebraicGeometry.IsReduced RelativeSegre.incidenceScheme
#synth AlgebraicGeometry.IsClosedImmersion RelativeSegre.incidenceInclusion
#print axioms GeneralCao.prescribed_metric_tensor_adjoint_extension_all_m
#print axioms GeneralCao.AnalyticLine.tensorBundleHomeomorph
#print axioms RelativeSegre.incidenceFunctorPoint

open Lean in
run_cmd do
  let env ← getEnv
  let roots : Array Name := #[``GlobalLineBundle.prescribed_semipositive_metric_nonextension,
    ``GlobalLineBundle.no_semipositive_extension_same_local_singularity_type,
    ``FixedFiberBundle.centralH0_hasMinimalSingularities,
    ``FixedFiberBundle.centralH0_current_lelong_half,
    ``FixedFiberBundle.first_nonzero_central_integrable_adjoint_exponent,
    ``GeneralCao.prescribed_metric_tensor_adjoint_extension_all_m,
    ``GeneralCao.AnalyticLine.tensorBundleHomeomorph,
    ``RelativeSegre.incidenceFunctorPoint,
    ``RelativeSegre.incidenceScheme_isReduced,
    ``BlowdownComplement.localizedIncidenceOpenIso]
  let mut pending := roots
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if !seen.contains n then
      seen := seen.insert n
      if let some info := env.find? n then
        let mut deps := info.type.getUsedConstants
        if let some v := info.value? then
          deps := deps ++ v.getUsedConstants
        let projectDeps := deps.filter (fun d => (`FailureOfSemipositiveMetricExtension).isPrefixOf d)
        logInfo m!"PROJECT_PROOF_DEPENDENCIES {n}: {projectDeps.qsort Name.lt}"
        pending := pending ++ projectDeps
  logInfo m!"ENDPOINT_DEPENDENCY_GRAPH_COMPLETE nodes={seen.size}"
