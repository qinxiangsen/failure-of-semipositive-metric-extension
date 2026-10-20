# Paper–source correspondence

For *Failure of semipositive metric extension in a smooth projective family*.

## Manuscript baseline

This release corresponds to the historically verified manuscript `failure_semipositive_metric_extension_final(1).tex`, SHA-256 **`dfba014b5838efd2bfb74994f2ca68113b285af56be6dd4356601e1a6e1014f9`**. All labels, numbers and line references below belong to that manuscript, not to a later revision.

The 44 historical inventory items have been checked against the actual archived Lean source: all cited full declaration names were located by their namespace and all renamed source paths were checked. Two items are non-proof material. The number 44 is an inventory count, not a count of independent theorems.

Each source snapshot remains independent. The full declaration names use the release prefix `FailureOfSemipositiveMetricExtension`; original namespace prefixes are described in `provenance/SOURCE_VERSIONS.md`. A declaration appearing in more than one snapshot is not evidence that the snapshots have been merged into one project.

**Verification status:** the entries below record source correspondence and historical acceptance, not an automatic claim of fresh compilation. The separate build report identifies what was compiled in this release, what relies on historical records, and what was checked only for file integrity. Compilation, integrity and mathematical correspondence are distinct checks.

**External inputs:** A01–A12 are explicitly admitted classical mathematical inputs; S01–S12 are the separately stated semantic interpretations. They are detailed in [EXTERNAL_INPUTS.md](EXTERNAL_INPUTS.md). The lists below identify relevant inputs; they are not asserted to be exact transitive axiom closures. For the exact closure of a particular endpoint, consult its recorded `#print axioms` output. For example, the E07 analytic Theorem A endpoint uses A01–A05 as mathematical axioms; its conventional algebraic interpretation also uses semantic bridges. Lean logical axioms are listed separately in the external-input document.

Source links are relative to the repository root. Stable inventory IDs identify the source correspondence items.

## D01: Weights, restrictions and singularity type

- Paper: §1, lines 78–90.
- `FailureOfSemipositiveMetricExtension.BlowupLineBundle.core`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/BlowupLineBundle.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/BlowupLineBundle.lean).
- `FailureOfSemipositiveMetricExtension.BlowupLineBundle.core_isContMDiff`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/BlowupAnalyticBundle.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/BlowupAnalyticBundle.lean).
- `FailureOfSemipositiveMetricExtension.BlowupLineBundle.actual_analytic_vectorBundle`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/BlowupAnalyticBundle.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/BlowupAnalyticBundle.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.SmoothHermitianMetric`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/FiberHermitianMetric.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/FiberHermitianMetric.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.metricNormSq_localTriv`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/FiberHermitianMetric.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/FiberHermitianMetric.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.SingularHermitianWeight`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/SingularHermitianWeights.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/SingularHermitianWeights.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.centralH0`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralSingularWeight.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralSingularWeight.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.centralH0_square`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralSingularWeight.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralSingularWeight.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.centralH0_upperSemicontinuousOn`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralWeightSemicontinuity.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralWeightSemicontinuity.lean).
- `FailureOfSemipositiveMetricExtension.GlobalLineBundle.SingularWeightOn`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalSingularWeights.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalSingularWeights.lean).
- `FailureOfSemipositiveMetricExtension.GlobalLineBundle.SingularWeightOn.centralRestriction`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalSingularWeights.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalSingularWeights.lean).
- `FailureOfSemipositiveMetricExtension.GlobalLineBundle.SingularWeightOn.centralDominatesH0`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalSingularWeights.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalSingularWeights.lean).
- `FailureOfSemipositiveMetricExtension.GlobalLineBundle.SingularWeightOn.centralExactH0`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalSingularWeights.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalSingularWeights.lean).
- Relevant external inputs: S08.
- Historical evidence: E01.
- Historical status: `accepted_with_standard_language_translation`.
- Scope: Compatible actual holomorphic line-bundle weights, restriction and local bounded comparison are accepted; no additional novel metric-definition proof.

## D02: Curvature, multiplier-ideal and canonical-bundle conventions

- Paper: §2, lines 145–164.
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.holomorphicSheaf`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/HolomorphicStalks.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/HolomorphicStalks.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.HolomorphicStalk`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/HolomorphicStalks.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/HolomorphicStalks.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.divisorPowerStalkIdeal`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralDivisorIdeals.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralDivisorIdeals.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.ellPowerStalkIdeal_normal`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralNormalIdeals.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralNormalIdeals.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiber.canonicalFiberFormEquiv`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/FixedFiberCanonicalTangentForms.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/FixedFiberCanonicalTangentForms.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.ambientCanonicalFormEquiv`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/FixedFiberCanonicalTangentForms.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/FixedFiberCanonicalTangentForms.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.adjointCore`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/FixedFiberCanonicalAdjoint.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/FixedFiberCanonicalAdjoint.lean).
- `FailureOfSemipositiveMetricExtension.Multiplier.IntegrableGerm`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/MultiplierGerms.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/MultiplierGerms.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.centralMultiplierIdealSheaf`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralMultiplierSheaf.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralMultiplierSheaf.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalCanonical.canonicalFiberFormEquiv`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalCanonicalTangentForms.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalCanonicalTangentForms.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalAdjoint.core`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalAdjointBundle.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalAdjointBundle.lean).
- `FailureOfSemipositiveMetricExtension.GeneralCao.TensorCentralAdjointSection`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GeneralTensorAdjointSections.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GeneralTensorAdjointSections.lean).
- `FailureOfSemipositiveMetricExtension.GeneralCao.TensorTotalAdjointSection`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GeneralTensorAdjointSections.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GeneralTensorAdjointSections.lean).
- `FailureOfSemipositiveMetricExtension.GeneralCao.AnalyticLine.tensorBundleHomeomorph`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GeneralTensorBundleIsomorphism.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GeneralTensorBundleIsomorphism.lean).
- Relevant external inputs: S08, S09.
- Historical evidence: E01.
- Historical status: `accepted_with_standard_language_translation`.
- Scope: Actual canonical/tensor objects, integrable germs and normalization accepted. Generic divisor/current and topological-Chern comparison may be explicit standard inputs; independently quantified all-current claim tracked separately in SIU.

## LIT01: Source of Păun’s Question 38

- Paper: §1, lines 73–81.
- No standalone Lean declaration: this is an applicability/interpretation or non-proof item.
- Relevant external inputs: none additionally itemized; shared logical foundations and geometric conventions still apply.
- Historical evidence: not a compiler-evidence item.
- Historical status: `bibliography_not_lean_obligation`.
- Scope: Question38 and attribution checked in standard-input audit; not a mathematical axiom.

## MAIN: Theorem A: same-object counterexample

- Paper: Theorem A, thm:main; equation (1.1), eq:weight-comparison; lines 92–108.
- `FailureOfSemipositiveMetricExtension.PaperTheoremA.actual_analytic_counterexample`
  - Snapshot E07: [`snapshots/E07/FailureOfSemipositiveMetricExtension/TheoremAAnalyticAssembly.lean`](../snapshots/E07/FailureOfSemipositiveMetricExtension/TheoremAAnalyticAssembly.lean).
- Relevant external inputs: A01, A02, A03, A04, A05, S01, S02, S03, S04, S08, S09, S11, S12.
- Historical evidence: E01, E04, E06, E07.
- Historical status: `complete_relative_explicit_standard_bridges`.
- Scope: Same-object15-field actual analytic counterexample independently accepted; standard disc, Segre/Chow, projective-graph algebraization/birationality, Kaehler and metric-current interpretation bridges remain explicit. No pending paper-specific MAIN prerequisite.

## COR01: Exact and same-singularity-type nonextension

- Paper: §1, lines 110–116.
- `FailureOfSemipositiveMetricExtension.GlobalLineBundle.no_exact_semipositive_extension`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/MetricNonextension.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/MetricNonextension.lean).
- `FailureOfSemipositiveMetricExtension.GlobalLineBundle.no_semipositive_extension_same_local_singularity_type`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/LocalSingularityComparison.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/LocalSingularityComparison.lean).
- `FailureOfSemipositiveMetricExtension.GlobalLineBundle.SingularWeightOn.centralComparison_frame_transfer`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/LocalSingularityComparison.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/LocalSingularityComparison.lean).
- `FailureOfSemipositiveMetricExtension.GlobalLineBundle.SingularWeightOn.centralLocallyDominatesH0_dominates`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/LocalSingularityComparison.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/LocalSingularityComparison.lean).
- Relevant external inputs: none additionally itemized; shared logical foundations and geometric conventions still apply.
- Historical evidence: E01.
- Historical status: `accepted`.
- Scope: Actual every-neighbourhood exact and same-local-singularity-type exclusion; compact finite-cover maximum accepted.

## HIS01: Hisamoto Example 4.12: local product and metric extension

- Paper: §1, lines 119–133.
- `FailureOfSemipositiveMetricExtension.Hisamoto.hisamoto_example_4_12_local_extension`
  - Snapshot E11: [`snapshots/E11/FailureOfSemipositiveMetricExtension/HisamotoLocalExtensionEndpoint.lean`](../snapshots/E11/FailureOfSemipositiveMetricExtension/HisamotoLocalExtensionEndpoint.lean).
- Relevant external inputs: S10.
- Historical evidence: E11.
- Historical status: `complete_relative_explicit_standard_interpretations`.
- Scope: Independently accepted actual onepoint incidence blowup, actual entire ruling fibre and product-disc neighbourhood, H tensor O(E), pullback O(2), and exact extension for every compatible semipositive metric. Standard F1, divisor/degree and metric-language interpretations explicit; no Example4.13 assertion.

## CAO: Integrable adjoint extension from Cao

- Paper: Proposition 2.1, prop:obstruction, lines 167–183.
- `FailureOfSemipositiveMetricExtension.Literature.cao_extension_via_projective_immersion_psh_translation`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Literature/CaoProjectivePsh.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Literature/CaoProjectivePsh.lean).
- `FailureOfSemipositiveMetricExtension.GeneralCao.adjoint_obstruction`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GeneralAdjointObstruction.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GeneralAdjointObstruction.lean).
- `FailureOfSemipositiveMetricExtension.Literature.cao_extension_proper_disc_kahler_psh_translation`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Literature/CaoGeneralKahler.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Literature/CaoGeneralKahler.lean).
- Relevant external inputs: A06, S03.
- Historical evidence: E01.
- Historical status: `accepted_relative_sixth_standard_input`.
- Scope: Stage9 actual arbitrary-dimensional adjoint_obstruction relative to its explicit generic Cao interface; do not reprove Cao.

## ADJUNCTION: Adjunction by dt and positive tensor powers

- Paper: Proof of Proposition 2.1, lines 185–201.
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.sigmaAdjointMap_localTriv`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/FixedFiberCanonicalAdjoint.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/FixedFiberCanonicalAdjoint.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.sigmaAdjointWeightedDensity_locally_integrable`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/AdjointSectionIntegrability.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/AdjointSectionIntegrability.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalCanonical.adjunctionWithNormal_independent`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CanonicalAdjunctionForms.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CanonicalAdjunctionForms.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalCanonical.adjunctionEquiv`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CanonicalAdjunctionEquivalence.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CanonicalAdjunctionEquivalence.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalCanonical.adjunctionBundleHomeomorph`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CanonicalAdjunctionIsomorphism.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CanonicalAdjunctionIsomorphism.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalCanonical.adjunctionBundleHomeomorph_analytic`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CanonicalAdjunctionIsomorphism.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CanonicalAdjunctionIsomorphism.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalAdjoint.restriction_localTriv`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalAdjointSections.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalAdjointSections.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.sigma_global_norm_finite`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralCanonicalNorm.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralCanonicalNorm.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.sigma_compared_global_norm_finite`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/ComparedCanonicalNorm.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/ComparedCanonicalNorm.lean).
- `FailureOfSemipositiveMetricExtension.GeneralCao.multiplier_germs_finite_canonical_norm`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GeneralCanonicalNormMeasure.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GeneralCanonicalNormMeasure.lean).
- `FailureOfSemipositiveMetricExtension.GeneralCao.coordinateVolume_normal_last`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GeneralAdjunctionAlgebra.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GeneralAdjunctionAlgebra.lean).
- `FailureOfSemipositiveMetricExtension.GeneralCao.alternating_normal_last_first`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GeneralAdjunctionAlgebra.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GeneralAdjunctionAlgebra.lean).
- `FailureOfSemipositiveMetricExtension.GeneralCao.AnalyticLine.tensorBundleHomeomorph`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GeneralTensorBundleIsomorphism.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GeneralTensorBundleIsomorphism.lean).
- `FailureOfSemipositiveMetricExtension.GeneralCao.prescribed_metric_tensor_adjoint_extension_all_m`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GeneralTensorAdjointSections.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GeneralTensorAdjointSections.lean).
- Relevant external inputs: A06.
- Historical evidence: E01.
- Historical status: `accepted`.
- Scope: Actual normal-last dt, global adjunction, finite norm, true tensor powers and all positive m already accepted.

## POINTS: Four centres and disjoint sections

- Paper: §3, lines 208–219.
- `FailureOfSemipositiveMetricExtension.Coordinates.four_projective_points_distinct`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/ProjectivePoints.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/ProjectivePoints.lean).
- `FailureOfSemipositiveMetricExtension.ProjectivePlane.centreSection_contMDiff`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/ProjectivePlaneFamily.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/ProjectivePlaneFamily.lean).
- `FailureOfSemipositiveMetricExtension.ProjectivePlane.centreSection_ranges_disjoint`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/ProjectivePlaneFamily.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/ProjectivePlaneFamily.lean).
- `FailureOfSemipositiveMetricExtension.ProjectivePlane.centreSection_range_isClosed`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/ProjectivePlaneFamily.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/ProjectivePlaneFamily.lean).
- Relevant external inputs: none additionally itemized; shared logical foundations and geometric conventions still apply.
- Historical evidence: E01.
- Historical status: `accepted`.
- Scope: All six projective inequalities and actual disjoint closed holomorphic sections accepted.

## FAMILY: Simultaneous blowup family and its fibres

- Paper: §3, lines 220–231.
- `FailureOfSemipositiveMetricExtension.ProjectivePlane.familyProjection_isProperMap`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/ProjectivePlaneFamily.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/ProjectivePlaneFamily.lean).
- `FailureOfSemipositiveMetricExtension.ProjectivePlane.instIsManifoldPoint`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/ProjectivePlaneManifold.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/ProjectivePlaneManifold.lean).
- `FailureOfSemipositiveMetricExtension.ProjectivePlane.instCompactSpacePoint`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/ProjectivePlaneCompact.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/ProjectivePlaneCompact.lean).
- `FailureOfSemipositiveMetricExtension.Blowup.instIsManifoldPoint`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/BlowupManifold.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/BlowupManifold.lean).
- `FailureOfSemipositiveMetricExtension.Blowup.instT2SpacePoint`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/BlowupSeparation.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/BlowupSeparation.lean).
- `FailureOfSemipositiveMetricExtension.Blowup.projection_isProperMap`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/BlowupProper.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/BlowupProper.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.incidence_mk_iff`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalIncidence.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalIncidence.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.blowdown_projection_surjective`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalIncidence.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalIncidence.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.exceptionalFiberEquiv`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalIncidence.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalIncidence.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.totalLocus_isClosed`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalTopology.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalTopology.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.projection_isProperMap`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalTopology.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalTopology.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.instCompactSpaceFiber`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalTopology.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalTopology.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.global_charts_cover`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalCharts.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalCharts.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.instIsManifoldTotal`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalManifold.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalManifold.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.proper_analytic_submersion`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalSubmersion.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalSubmersion.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.projection_mfderiv_rightInverse`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalSubmersion.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalSubmersion.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiber.instIsManifoldFiber`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalFiberManifold.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalFiberManifold.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.CaoAdapter.family`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CaoFamilyAdapter.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CaoFamilyAdapter.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.CaoAdapter.immersion`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CaoImmersionAdapter.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CaoImmersionAdapter.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.BlowdownComplement.localizedIncidenceOpenIso`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalBlowdownAffineSchemes.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalBlowdownAffineSchemes.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.RelativeSegre.complexPointEquiv`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/RelativeIncidenceProjComparison.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/RelativeIncidenceProjComparison.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.RelativeSegre.incidenceFunctorPoint`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/RelativeIncidenceFunctorPoints.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/RelativeIncidenceFunctorPoints.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.RelativeSegre.incidenceScheme_isReduced`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/RelativeIncidenceReduced.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/RelativeIncidenceReduced.lean).
- `FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate.RawAdapter.GraphClosure.actual_blowup_graph_certificate`
  - Snapshot E12_E14: [`snapshots/E12_E14/FailureOfSemipositiveMetricExtension/CoordinateBlowupAdapter/ActualBlowupGraphCertificate.lean`](../snapshots/E12_E14/FailureOfSemipositiveMetricExtension/CoordinateBlowupAdapter/ActualBlowupGraphCertificate.lean).
- Relevant external inputs: S02, S11, S12.
- Historical evidence: E01, E04, E05, E06, E12, E14.
- Historical status: `complete_relative_explicit_standard_blowup_correspondences`.
- Scope: Same actual Total is identified with the specified simultaneous blowup analytification by the accepted polynomial graph, centre ideals and relative coordinate certificate plus explicit standard graph-closure/reduced-analytic comparison. Parameter and blowdown preserved; no native Scheme equivalence declaration.

## BUNDLES: Actual line bundles and divisor notation

- Paper: §3, lines 233–237.
- `FailureOfSemipositiveMetricExtension.GlobalLineBundle.core`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalLineBundle.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalLineBundle.lean).
- `FailureOfSemipositiveMetricExtension.GlobalLineBundle.core_isContMDiff`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalAnalyticLineBundle.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalAnalyticLineBundle.lean).
- `FailureOfSemipositiveMetricExtension.GlobalLineBundle.exceptionalSection`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalExceptionalSection.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalExceptionalSection.lean).
- `FailureOfSemipositiveMetricExtension.GlobalLineBundle.exceptionalSection_zero_iff`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalExceptionalSection.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalExceptionalSection.lean).
- `FailureOfSemipositiveMetricExtension.GlobalLineBundle.exceptionalSection_local_simple_zero`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalExceptionalOrder.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalExceptionalOrder.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.core`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalFiberLineBundle.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalFiberLineBundle.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.canonicalBundleHomeomorph`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/FixedFiberCanonicalIsomorphism.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/FixedFiberCanonicalIsomorphism.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.canonicalBundleHomeomorph_analytic`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/FixedFiberCanonicalIsomorphism.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/FixedFiberCanonicalIsomorphism.lean).
- `FailureOfSemipositiveMetricExtension.GlobalLineBundle.Hyperplane.actual_hyperplane_pullback_certificate`
  - Snapshot E08: [`snapshots/E08/FailureOfSemipositiveMetricExtension/GlobalHyperplanePullback.lean`](../snapshots/E08/FailureOfSemipositiveMetricExtension/GlobalHyperplanePullback.lean).
- `FailureOfSemipositiveMetricExtension.GlobalLineBundle.PaperDivisors.paperGain_eq_actual_gain`
  - Snapshot E08: [`snapshots/E08/FailureOfSemipositiveMetricExtension/PaperDivisorCocycles.lean`](../snapshots/E08/FailureOfSemipositiveMetricExtension/PaperDivisorCocycles.lean).
- `FailureOfSemipositiveMetricExtension.GlobalLineBundle.PaperDivisors.actual_exceptional_divisor_naming`
  - Snapshot E08: [`snapshots/E08/FailureOfSemipositiveMetricExtension/PaperDivisorCocycles.lean`](../snapshots/E08/FailureOfSemipositiveMetricExtension/PaperDivisorCocycles.lean).
- Relevant external inputs: S04.
- Historical evidence: E01, E08, E09, E10.
- Historical status: `complete_on_actual_incidence_relative_standard_divisor_correspondences`.
- Scope: Actual H pullback, E simple zero divisors, correctly signed same-object L/A/K/ell/Q cocycles and canonical transition independently accepted. Literal ell/Q strict-transform supports and pairwise distinct Q line sets independently accepted. Standard O(D), tensor/dual and irreducible-closure interpretations explicit.

## QUADRIC: Two quadratic forms

- Paper: Equation (3.1), eq:quadrics, lines 243–249.
- `FailureOfSemipositiveMetricExtension.Coordinates.quadrics_vanish`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Coordinates.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Coordinates.lean).
- Relevant external inputs: none additionally itemized; shared logical foundations and geometric conventions still apply.
- Historical evidence: E01.
- Historical status: `accepted`.
- Scope: Exact equations and four-centre vanishing accepted.

## EFFECTIVE: Effectivity of L on the total space

- Paper: Lemma 3.1, lem:psef, lines 239–251.
- `FailureOfSemipositiveMetricExtension.GlobalLineBundle.liftedPencil`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalPencilDivision.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalPencilDivision.lean).
- `FailureOfSemipositiveMetricExtension.GlobalLineBundle.liftedPencil_analytic`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalPencilDivision.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalPencilDivision.lean).
- `FailureOfSemipositiveMetricExtension.GlobalLineBundle.liftedPencil_no_basepoint`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalPencilGeneration.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalPencilGeneration.lean).
- Relevant external inputs: S04.
- Historical evidence: E01, E07.
- Historical status: `accepted_relative_standard_divisor_metric_fact`.
- Scope: New assembly produces nonzero global section on same L and on each nonzero fibre. Standard nonzero-section/effective-divisor/psh-divisor-metric implication suffices. Unaccepted increment2 is stronger, not required.

## COLLINEAR: Central collinearity and nearby noncollinearity

- Paper: §3, line 254.
- `FailureOfSemipositiveMetricExtension.Coordinates.determinants`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Coordinates.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Coordinates.lean).
- `FailureOfSemipositiveMetricExtension.Coordinates.no_three_collinear_determinants`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Coordinates.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Coordinates.lean).
- `FailureOfSemipositiveMetricExtension.Coordinates.central_collinearity`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Coordinates.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Coordinates.lean).
- Relevant external inputs: none additionally itemized; shared logical foundations and geometric conventions still apply.
- Historical evidence: E01, E02.
- Historical status: `accepted_increment1`.
- Scope: Genuine projective collinearity, not just determinants, has independent increment1 acceptance.

## NEARBASE: Nearby pencil and exceptional base-point check

- Paper: §3, lines 254–264.
- `FailureOfSemipositiveMetricExtension.Coordinates.nearby_common_zero_locus`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Coordinates.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Coordinates.lean).
- `FailureOfSemipositiveMetricExtension.Coordinates.nearby_chart_expansions`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Coordinates.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Coordinates.lean).
- `FailureOfSemipositiveMetricExtension.Coordinates.nearby_initial_terms`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Coordinates.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Coordinates.lean).
- `FailureOfSemipositiveMetricExtension.Coordinates.projective_common_zero_locus`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/ProjectivePoints.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/ProjectivePoints.lean).
- `FailureOfSemipositiveMetricExtension.PencilSections.nearby_systems_no_exceptional_basepoint`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/PencilSections.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/PencilSections.lean).
- `FailureOfSemipositiveMetricExtension.BlowupLineBundle.nearby_actual_sections_no_exceptional_basepoint`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/BlowupBundleSections.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/BlowupBundleSections.lean).
- `FailureOfSemipositiveMetricExtension.GlobalLineBundle.pencilLocalCoefficient_no_basepoint`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalPencilGeneration.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalPencilGeneration.lean).
- `FailureOfSemipositiveMetricExtension.GlobalLineBundle.liftedPencil_no_basepoint`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalPencilGeneration.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalPencilGeneration.lean).
- Relevant external inputs: none additionally itemized; shared logical foundations and geometric conventions still apply.
- Historical evidence: E01.
- Historical status: `accepted`.
- Scope: Actual common zeros, all exceptional initial terms, actual nearby global sections with no common zero accepted.

## NEARNEF: Nearby generation, nefness and pullback description

- Paper: §3, lines 264–269.
- `FailureOfSemipositiveMetricExtension.GlobalLineBundle.liftedPencil_generates`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalPencilGeneration.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalPencilGeneration.lean).
- `FailureOfSemipositiveMetricExtension.GlobalLineBundle.fibrePencil_no_basepoint`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalPencilGeneration.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalPencilGeneration.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.nearbyLMetric`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GeneratedFiberMetrics.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GeneratedFiberMetrics.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.nearbyLMetric_plurisubharmonic`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/MetricPlurisubharmonicity.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/MetricPlurisubharmonicity.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil.pencilBundleHomeomorph`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/NearbyPencilBundleIsomorphism.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/NearbyPencilBundleIsomorphism.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil.pencilBundleHomeomorph_analytic`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/NearbyPencilBundleIsomorphism.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/NearbyPencilBundleIsomorphism.lean).
- Relevant external inputs: S06.
- Historical evidence: E01.
- Historical status: `accepted_relative_standard_generated_implies_nef`.
- Scope: Actual global generation and actual pullback of O(1) accepted. Standard nef theorem exempt; do not enumerate curves.

## INTERSECTION: Intersection and canonical-class formulas

- Paper: Equation (3.2), eq:nearby-intersections, lines 269–274.
- `FailureOfSemipositiveMetricExtension.L_square`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean).
- `FailureOfSemipositiveMetricExtension.K_dot_L`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.ambientCanonicalFormEquiv_localTriv`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/FixedFiberCanonicalTangentForms.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/FixedFiberCanonicalTangentForms.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiber.tangentCoordinateForm_canonicalGain`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/FixedFiberCanonicalTangentForms.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/FixedFiberCanonicalTangentForms.lean).
- Relevant external inputs: S06, S11.
- Historical evidence: E01, E08, E14.
- Historical status: `complete_relative_explicit_standard_blowup_correspondences`.
- Scope: Accepted actual H/E/K naming and R1 specified smooth point-blowup identity make the standard intersection/canonical formulas applicable; displayed numerical calculations and actual restriction/normal degrees were independently accepted. No general intersection theory rebuilt.

## VANISHING: Vanishing of every nearby adjoint system

- Paper: Lemma 3.2, lem:vanishing, lines 275–286.
- `FailureOfSemipositiveMetricExtension.adjoint_intersection`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean).
- `FailureOfSemipositiveMetricExtension.adjoint_intersection_negative`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil.Conic.restrictionBundleHomeomorph`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GenericConicBundleIsomorphism.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GenericConicBundleIsomorphism.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil.Conic.genericLocus_dense`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GenericConicDensity.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GenericConicDensity.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.adjointBundleHomeomorph`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/FixedFiberAdjointIsomorphism.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/FixedFiberAdjointIsomorphism.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.actual_nearby_adjoint_section_zero`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/FixedFiberAdjointVanishing.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/FixedFiberAdjointVanishing.lean).
- Relevant external inputs: none additionally itemized; shared logical foundations and geometric conventions still apply.
- Historical evidence: E01.
- Historical status: `accepted`.
- Scope: Every actual nearby K tensor L^m section vanishes, proved analytically without intersection-theory assumption.

## CENTRALCLASS: The central curve and A=2L−ell

- Paper: §3, lines 288–294.
- `FailureOfSemipositiveMetricExtension.A_definition`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.ellCurve_biholomorphic`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralCurveEmbedding.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralCurveEmbedding.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.ellCurve_compact_analytic_embedded`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralCurveEmbedding.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralCurveEmbedding.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.ell_restriction_cocycle`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralCurveRestriction.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralCurveRestriction.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.restrictionLift_isClosedEmbedding`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralCurveRestrictedTotal.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralCurveRestrictedTotal.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.CurveNormal.degreeHomeomorph`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralCurveNormalIsomorphism.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralCurveNormalIsomorphism.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.PaperStrictTransforms.ell_is_literal_strict_transform`
  - Snapshot E09_E10: [`snapshots/E09_E10/FailureOfSemipositiveMetricExtension/PaperStrictTransformCertificate.lean`](../snapshots/E09_E10/FailureOfSemipositiveMetricExtension/PaperStrictTransformCertificate.lean).
- Relevant external inputs: S04, S05.
- Historical evidence: E01, E08, E09, E10.
- Historical status: `complete_on_actual_incidence_relative_standard_divisor_correspondences`.
- Scope: Actual embedded ell is literal closure of the original z=0 line off centres, with simple zeros, normal O(-2), correct H/E class and actual A+ell=2L cocycle. Standard divisor/normal-degree interpretations explicit.

## CUBICSPAN: Complete span of the four cubics

- Paper: Lemma 3.3, lem:bpf; equation (3.3), eq:A-generators, lines 296–310.
- `FailureOfSemipositiveMetricExtension.Cubics.cubic_span`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Cubics.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Cubics.lean).
- `FailureOfSemipositiveMetricExtension.Jets.cubic_span_of_first_jet`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Jets.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Jets.lean).
- `FailureOfSemipositiveMetricExtension.Jets.cubic_doubleAtP4_iff_first_jet`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Jets.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Jets.lean).
- `FailureOfSemipositiveMetricExtension.Jets.cubic_doubleAtP4_iff_mem_originIdeal_sq`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Jets.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Jets.lean).
- Relevant external inputs: S07, S11.
- Historical evidence: E01, E08, E14.
- Historical status: `complete_relative_explicit_standard_blowup_correspondences`.
- Scope: Explicit cubic coefficient span and assigned-multiplicity jet equivalence independently accepted; R1/R2 now supply exact blowup and A identity for standard polynomial-section correspondence. Stronger unaccepted all-holomorphic-section classification is not used.

## CUBICBASE: Common zero locus of the cubics

- Paper: Proof of Lemma 3.3, lines 306–310.
- `FailureOfSemipositiveMetricExtension.Cubics.generators_common_zero_locus`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Cubics.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Cubics.lean).
- `FailureOfSemipositiveMetricExtension.Coordinates.projective_cubic_common_zero_locus`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/ProjectivePoints.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/ProjectivePoints.lean).
- Relevant external inputs: none additionally itemized; shared logical foundations and geometric conventions still apply.
- Historical evidence: E01.
- Historical status: `accepted`.
- Scope: Actual projective zero locus accepted.

## CENTRALJETS: Exceptional initial terms and jets

- Paper: Proof of Lemma 3.3, lines 310–316.
- `FailureOfSemipositiveMetricExtension.BlowupSections.all_cubic_divided_pullbacks`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/BlowupSections.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/BlowupSections.lean).
- `FailureOfSemipositiveMetricExtension.BlowupLineBundle.central_actual_sections_no_exceptional_basepoint`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/BlowupBundleSections.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/BlowupBundleSections.lean).
- Relevant external inputs: none additionally itemized; shared logical foundations and geometric conventions still apply.
- Historical evidence: E01.
- Historical status: `accepted`.
- Scope: Divided chart polynomials and no exceptional common zeros accepted.

## ABPF: Actual base-point-free system A

- Paper: Lemma 3.3, lem:bpf, lines 296–317.
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.liftedCentralCubics`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralCubicDivision.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralCubicDivision.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.liftedCentralCubics_analytic`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralCubicDivision.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralCubicDivision.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.liftedCentralCubics_division_sectionMap`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralCubicDivision.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralCubicDivision.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.liftedCentralCubics_basepoint_free`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralCubicDivision.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralCubicDivision.lean).
- Relevant external inputs: none additionally itemized; shared logical foundations and geometric conventions still apply.
- Historical evidence: E01.
- Historical status: `accepted`.
- Scope: Four actual global analytic sections generate at every central point; complete linear system therefore basepoint-free without separately proving it has dimension4.

## METRIC: Prescribed semipositive metric and singularities

- Paper: Equation (3.4), eq:central-metric, lines 319–329.
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.generatedMetric`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/FiberHermitianMetric.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/FiberHermitianMetric.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.centralAMetric`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GeneratedFiberMetrics.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GeneratedFiberMetrics.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.centralAMetric_smooth`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GeneratedFiberMetrics.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GeneratedFiberMetrics.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.centralAMetric_formula`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GeneratedFiberMetrics.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GeneratedFiberMetrics.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.centralH0_square`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralSingularWeight.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralSingularWeight.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.centralH0_local_normal_form`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralSingularRegularity.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralSingularRegularity.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.centralH0_plurisubharmonic`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/MetricPlurisubharmonicity.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/MetricPlurisubharmonicity.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.centralAMetric_plurisubharmonic`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/MetricPlurisubharmonicity.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/MetricPlurisubharmonicity.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.centralH0_analytic_singularities`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/AnalyticSingularities.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/AnalyticSingularities.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.centralH0_logarithmic_order`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralLogarithmicOrder.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralLogarithmicOrder.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.centralH0_curvatureCurrent`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralCurvatureLelong.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralCurvatureLelong.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.centralH0_current_lelong_half`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralCurvatureLelong.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralCurvatureLelong.lean).
- Relevant external inputs: A02, A05, S04, S08, S09.
- Historical evidence: E01.
- Historical status: `accepted_relative_standard_FS_current_inputs`.
- Scope: Same centralH0, square identity, smooth part, psh, analytic singularities, exact support and genuine local trace-mass Lelong1/2 accepted.

## ZARISKI_NUM: Zariski numerical identities

- Paper: Equation (3.5), eq:zariski, lines 330–337.
- `FailureOfSemipositiveMetricExtension.zariski_vector_identity`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean).
- `FailureOfSemipositiveMetricExtension.A_dot_ell`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean).
- `FailureOfSemipositiveMetricExtension.ell_square`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean).
- Relevant external inputs: S06.
- Historical evidence: E01.
- Historical status: `accepted_arithmetic_and_actual_restriction_degrees`.
- Scope: L=(A+ell)/2, A degree0 on ell, actual normal O(-2) and L degree-1 accepted. Geometric decomposition via standard uniqueness/Boucksom, not fresh theory.

## ZARISKI_GEOM: Geometric Zariski-decomposition applicability

- Paper: §3, lines 330–340.
- No standalone Lean declaration: this is an applicability/interpretation or non-proof item.
- Relevant external inputs: A04.
- Historical evidence: E01, E08, E09, E10.
- Historical status: `complete_for_metric_application_relative_standard_geometric_interpretation`.
- Scope: Generic negative-curve metric interface already accepted with actual degrees/sections. Concrete R2 divisor names now independently accepted, so classical Picard/Zariski wording uses only explicit standard correspondences; independently quantified arbitrary current intermediate remains separately SIU/R3.

## SIU: Positive residual of an independent current

- Paper: Equation (3.6), eq:divisorial-bound, lines 338–348.
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.FreshCurrentBridge.actual_independent_current_full_residual`
  - Snapshot E13: [`snapshots/E13/FailureOfSemipositiveMetricExtension/IndependentCurrentCompleteEndpoint.lean`](../snapshots/E13/FailureOfSemipositiveMetricExtension/IndependentCurrentCompleteEndpoint.lean).
- Relevant external inputs: A02, A04, A05, A07, A08, A09, A10, A11, A12, S03, S08, S09.
- Historical evidence: E01, E13.
- Historical status: `complete_relative_explicit_standard_current_inputs`.
- Scope: Independent T quantified first; same reconstructed h, retained residual r and concrete global u; literal positive T-[ell]/2, class A/2, all-test coefficient identity and trace-Lelong bound independently accepted. Nine mathematical standard inputs, six newly introduced in R3; real c1 identification remains explicit Chern–Weil interpretation.

## MINIMAL: Global potential and minimal singularities

- Paper: §3, lines 347–360.
- `FailureOfSemipositiveMetricExtension.usc_withBot_bounded_above`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Semicontinuity.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Semicontinuity.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.relativePotential`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/MetricRelativePotential.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/MetricRelativePotential.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.relativePotential_upperSemicontinuous`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/MetricRelativePotential.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/MetricRelativePotential.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.weight_le_smooth_add_const`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/MetricRelativePotential.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/MetricRelativePotential.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.HalfDivisorResidual`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralResidualMinimality.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralResidualMinimality.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.central_weight_le_h0_of_residual`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralResidualMinimality.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralResidualMinimality.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.centralH0_minimal_of_residual_decompositions`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralResidualMinimality.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralResidualMinimality.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.halfDivisorResidual_exists`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralMetricMinimality.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralMetricMinimality.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.centralH0_hasMinimalSingularities`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralMetricMinimality.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralMetricMinimality.lean).
- Relevant external inputs: A02, A04.
- Historical evidence: E01.
- Historical status: `accepted_relative_standard_negative_curve_input`.
- Scope: Actual every-psh-metric minimality and global bounded comparison accepted. Paper all-independent-current intermediate remains separately SIU, not assumed by the main theorem.

## RADIAL: Strict integrability threshold

- Paper: Proof of Lemma 3.4, lines 378–385.
- `FailureOfSemipositiveMetricExtension.radial_integrability_iff`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Integrability.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Integrability.lean).
- `FailureOfSemipositiveMetricExtension.threshold_equivalence`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Integrability.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Integrability.lean).
- `FailureOfSemipositiveMetricExtension.fourth_power_threshold`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Integrability.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Integrability.lean).
- `FailureOfSemipositiveMetricExtension.complex_disc_integrability_iff`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/ComplexIntegrability.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/ComplexIntegrability.lean).
- `FailureOfSemipositiveMetricExtension.complex_punctured_disc_integrability_iff`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/ComplexIntegrability.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/ComplexIntegrability.lean).
- `FailureOfSemipositiveMetricExtension.continuous_unit_local_integrability_iff`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/ComplexIntegrability.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/ComplexIntegrability.lean).
- `FailureOfSemipositiveMetricExtension.continuous_positive_unit_local_integrability_iff`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/ComplexIntegrability.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/ComplexIntegrability.lean).
- Relevant external inputs: none additionally itemized; shared logical foundations and geometric conventions still apply.
- Historical evidence: E01.
- Historical status: `accepted`.
- Scope: Actual normal radial and complex polydisc integrability thresholds accepted.

## IDEAL: Multiplier ideal for every positive exponent

- Paper: Lemma 3.4, lem:ideal; equation (3.7), eq:multiplier-ideal, lines 362–389.
- `FailureOfSemipositiveMetricExtension.complex_polydisc_integrability_iff`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/ProductIntegrability.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/ProductIntegrability.lean).
- `FailureOfSemipositiveMetricExtension.continuous_positive_unit_polydisc_local_integrability_iff`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/ProductIntegrability.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/ProductIntegrability.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.ellPowerStalkIdeal_normal`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralNormalIdeals.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralNormalIdeals.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.normalUnitGerm_isUnit`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralNormalIdeals.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralNormalIdeals.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.sigmaSection_germ_mem_ellSquare`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralDivisorIdeals.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralDivisorIdeals.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.ellSection_simple_equation`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralSimpleDivisor.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralSimpleDivisor.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.centralH0_multiplierGerm_iff`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralMultiplierStalks.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralMultiplierStalks.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.centralMultiplierStalkIdeal_eq`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralMultiplierStalks.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralMultiplierStalks.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.centralMultiplierIdealSheaf_eq`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralMultiplierSheaf.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralMultiplierSheaf.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.ellIdealSections_locally_principal`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralMultiplierSheaf.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralMultiplierSheaf.lean).
- Relevant external inputs: A03, S04.
- Historical evidence: E01.
- Historical status: `accepted_relative_standard_SNC_and_divisor_ideal_correspondence`.
- Scope: Actual all-point multiplier ideal/stalk equality with power of real ell equation accepted. O(-k ell) naming follows standard effective-divisor ideal correspondence; no need repair full general negative-divisor API.

## QCLASS: Q as three reduced strict transforms and its class

- Paper: Equation (3.8), eq:Q-class, lines 393–401.
- `FailureOfSemipositiveMetricExtension.Q_sum`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean).
- `FailureOfSemipositiveMetricExtension.Q_adjoint`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean).
- `FailureOfSemipositiveMetricExtension.Q_two_A`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.qSection`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralAuxiliarySections.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralAuxiliarySections.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.sigmaSection`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralAdjointSection.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralAdjointSection.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.sigmaSection_germ_factorization`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralDivisorIdeals.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralDivisorIdeals.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.sigmaGain_canonical_four_L`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/FixedFiberCanonicalAdjoint.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/FixedFiberCanonicalAdjoint.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.PaperStrictTransforms.Q_is_three_literal_strict_transforms`
  - Snapshot E09_E10: [`snapshots/E09_E10/FailureOfSemipositiveMetricExtension/PaperStrictTransformCertificate.lean`](../snapshots/E09_E10/FailureOfSemipositiveMetricExtension/PaperStrictTransformCertificate.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.PaperStrictTransforms.Q_reduced_local_equation`
  - Snapshot E09_E10: [`snapshots/E09_E10/FailureOfSemipositiveMetricExtension/PaperStrictTransformCertificate.lean`](../snapshots/E09_E10/FailureOfSemipositiveMetricExtension/PaperStrictTransformCertificate.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.PaperStrictTransforms.named_projective_line_sets_pairwise_distinct`
  - Snapshot E09_E10: [`snapshots/E09_E10/FailureOfSemipositiveMetricExtension/DistinctCentralLines.lean`](../snapshots/E09_E10/FailureOfSemipositiveMetricExtension/DistinctCentralLines.lean).
- Relevant external inputs: S04, S05.
- Historical evidence: E01, E03, E08, E09, E10.
- Historical status: `complete_on_actual_incidence_relative_standard_divisor_correspondences`.
- Scope: Actual q support equals union of three literal strict-transform closures; explicit off-centre projective witnesses distinguish all three components; actual local q equation has surjective derivative and nowherezero denominator. Combined with accepted K+4L and sigma=ell^2 Q cocycles gives stated reduced divisor/class under standard correspondences.

## SECTION: Nonzero integrable central adjoint section

- Paper: Equation (3.9), eq:central-section, lines 402–410.
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.sigmaSection`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralAdjointSection.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralAdjointSection.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.sigmaSection_nonzero`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralAdjointSection.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralAdjointSection.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.sigmaWeightedDensity_locally_integrable`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralSectionIntegrability.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralSectionIntegrability.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.sigmaAdjointMap`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/FixedFiberCanonicalAdjoint.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/FixedFiberCanonicalAdjoint.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.sigmaAdjointMap_contMDiff`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/FixedFiberCanonicalAdjoint.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/FixedFiberCanonicalAdjoint.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.sigmaAdjoint_nonzero`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/FixedFiberCanonicalAdjoint.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/FixedFiberCanonicalAdjoint.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.sigmaAdjointGerm_weighted_integrable`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/AdjointSectionIntegrability.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/AdjointSectionIntegrability.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.sigmaAdjointWeightedDensity_locally_integrable`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/AdjointSectionIntegrability.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/AdjointSectionIntegrability.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.centralCanonicalNormMeasure`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralCanonicalNorm.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralCanonicalNorm.lean).
- Relevant external inputs: A03.
- Historical evidence: E01.
- Historical status: `accepted`.
- Scope: Actual nonzero canonical L^4 section, genuine all-frame weighted integrability, finite global norm accepted.

## SHRINK: Shrinking a neighbourhood to full nearby fibres

- Paper: Proof of Theorem A, lines 416–421.
- `FailureOfSemipositiveMetricExtension.proper_fiber_neighborhood`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Topology.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Topology.lean).
- `FailureOfSemipositiveMetricExtension.Blowup.fiber_neighborhood`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/BlowupProper.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/BlowupProper.lean).
- `FailureOfSemipositiveMetricExtension.ProjectivePlane.familyProjection_isProperMap`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/ProjectivePlaneFamily.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/ProjectivePlaneFamily.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.global_fiber_neighborhood`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalTopology.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalTopology.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.contains_full_fibres_near_zero`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/FamilyNeighbourhoods.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/FamilyNeighbourhoods.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.contains_full_disc_near_zero`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/FamilyNeighbourhoods.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/FamilyNeighbourhoods.lean).
- Relevant external inputs: none additionally itemized; shared logical foundations and geometric conventions still apply.
- Historical evidence: E01.
- Historical status: `accepted`.
- Scope: Any neighbourhood containing entire central fibre contains full small-parameter fibres, proved from actual properness.

## COMPARE: One-sided weight comparison and integrability

- Paper: Proof of Theorem A, lines 423–426.
- `FailureOfSemipositiveMetricExtension.weight_comparison`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Integrability.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Integrability.lean).
- `FailureOfSemipositiveMetricExtension.tensor_weight_comparison`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Integrability.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Integrability.lean).
- `FailureOfSemipositiveMetricExtension.integrable_weighted_of_comparison`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Integrability.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Integrability.lean).
- `FailureOfSemipositiveMetricExtension.Multiplier.IntegrableGerm.mono_of_comparison`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/MultiplierComparison.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/MultiplierComparison.lean).
- `FailureOfSemipositiveMetricExtension.Multiplier.IntegrableGerm.mono_of_local_comparison`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/MultiplierComparison.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/MultiplierComparison.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.sigmaAdjointGerm_integrable_of_extension_comparison`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/AdjointSectionIntegrability.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/AdjointSectionIntegrability.lean).
- Relevant external inputs: none additionally itemized; shared logical foundations and geometric conventions still apply.
- Historical evidence: E01.
- Historical status: `accepted`.
- Scope: One-sided extended weight inequality implies true germ integrability including minus-infinity behavior.

## EXTEND: Application of Cao at the fourth power

- Paper: Proof of Theorem A, lines 426–431.
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.sigmaAdjointGerm_integrable_of_extension_comparison`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/AdjointSectionIntegrability.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/AdjointSectionIntegrability.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.CaoAdapter.sigmaCentralSection_inRestrictedMultiplier`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/AdjointMultiplierFrameChange.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/AdjointMultiplierFrameChange.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.CaoAdapter.fourthPowerWeight`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/FourthPowerWeights.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/FourthPowerWeights.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.CaoAdapter.fourthPowerWeight_wellDefined`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/FourthPowerWeights.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/FourthPowerWeights.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.CaoAdapter.extractSection_restrictsByDt`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CaoDtRestrictionAdapter.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CaoDtRestrictionAdapter.lean).
- Relevant external inputs: A01.
- Historical evidence: E01.
- Historical status: `accepted_relative_standard_Cao`.
- Scope: Actual fourth-power metric, finite restriction, global norm and dt hypotheses verified; Cao is explicit input.

## DENSE: Density and vanishing of the extended section

- Paper: Proof of Theorem A, lines 432–436.
- `FailureOfSemipositiveMetricExtension.dense_noncentral_fibers`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Topology.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Topology.lean).
- `FailureOfSemipositiveMetricExtension.equality_from_noncentral_fibers`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Topology.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Topology.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.projection_isOpenMap`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalLocalSections.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/GlobalLocalSections.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.noncentral_fibres_dense`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/FamilyNeighbourhoods.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/FamilyNeighbourhoods.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalAdjoint.actual_central_restriction_zero`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/AdjointSectionNonextension.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/AdjointSectionNonextension.lean).
- Relevant external inputs: none additionally itemized; shared logical foundations and geometric conventions still apply.
- Historical evidence: E01.
- Historical status: `accepted`.
- Scope: Actual noncentral fibres dense; bundle section vanishing on them implies central zero.

## SECTION_NONEXT: No holomorphic neighbourhood extension of the adjoint section

- Paper: §3, lines 392–436.
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalAdjoint.actual_sigma_section_has_no_neighbourhood_extension`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/AdjointSectionNonextension.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/AdjointSectionNonextension.lean).
- Relevant external inputs: none additionally itemized; shared logical foundations and geometric conventions still apply.
- Historical evidence: E01.
- Historical status: `accepted`.
- Scope: Genuine sigma has no neighbourhood holomorphic adjoint extension, no nonstandard axioms.

## NONEXT: Metric nonextension on every central neighbourhood

- Paper: Proof of Theorem A, lines 412–437.
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalAdjoint.sigma_adjoint_has_no_neighbourhood_extension`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/AdjointSectionNonextension.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/AdjointSectionNonextension.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalAdjoint.actual_sigma_section_has_no_neighbourhood_extension`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/AdjointSectionNonextension.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/AdjointSectionNonextension.lean).
- `FailureOfSemipositiveMetricExtension.GlobalLineBundle.no_semipositive_metric_dominating_centralH0`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/MetricNonextension.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/MetricNonextension.lean).
- `FailureOfSemipositiveMetricExtension.GlobalLineBundle.prescribed_semipositive_metric_nonextension`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/MetricNonextension.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/MetricNonextension.lean).
- Relevant external inputs: A01.
- Historical evidence: E01.
- Historical status: `accepted_relative_standard_inputs`.
- Scope: Actual full all-neighbourhood metric comparison obstruction accepted; new assembly joins it to same geometry and metric.

## SMALL_NUM: Small-exponent divisor calculations

- Paper: §4, lines 441–448.
- `FailureOfSemipositiveMetricExtension.integrable_adjoint_one`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean).
- `FailureOfSemipositiveMetricExtension.integrable_adjoint_two`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean).
- `FailureOfSemipositiveMetricExtension.integrable_adjoint_three`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean).
- `FailureOfSemipositiveMetricExtension.integrable_adjoint_four`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean).
- Relevant external inputs: S04.
- Historical evidence: E01, E08, E09, E10.
- Historical status: `complete_on_actual_incidence_relative_standard_divisor_correspondences`.
- Scope: Displayed m1,m2,m3,m4 divisor arithmetic now has accepted actual H/E/ell/Q/L/K naming. Standard tensor, dual and divisor-ideal correspondence supplies the geometric class wording; independently accepted actual section-vanishing/IsLeast endpoints unchanged.

## SMALL12: Vanishing at m=1 and m=2

- Paper: §4, lines 449–451.
- `FailureOfSemipositiveMetricExtension.minus_H_degree`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.actual_central_small_integrable_adjoint_section_zero`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralSmallIntegrableAdjointVanishing.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralSmallIntegrableAdjointVanishing.lean).
- Relevant external inputs: none additionally itemized; shared logical foundations and geometric conventions still apply.
- Historical evidence: E01.
- Historical status: `accepted`.
- Scope: Arbitrary actual integrable adjoint sections vanish at m1 and2.

## SMALL3: Conic impossibility at m=3

- Paper: §4, lines 451–455.
- `FailureOfSemipositiveMetricExtension.Cubics.conic_impossible`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Cubics.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Cubics.lean).
- `FailureOfSemipositiveMetricExtension.Cubics.conic_eval_zero`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Cubics.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Cubics.lean).
- `FailureOfSemipositiveMetricExtension.Jets.conic_eval_zero_of_first_jet`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Jets.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Jets.lean).
- `FailureOfSemipositiveMetricExtension.Jets.conic_doubleAtP4_iff_mem_originIdeal_sq`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Jets.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Jets.lean).
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.actual_central_small_integrable_adjoint_section_zero`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralSmallIntegrableAdjointVanishing.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralSmallIntegrableAdjointVanishing.lean).
- Relevant external inputs: none additionally itemized; shared logical foundations and geometric conventions still apply.
- Historical evidence: E01.
- Historical status: `accepted`.
- Scope: Actual third system vanishing plus conic coefficient/jet argument accepted.

## FIRST4: First nonzero integrable adjoint exponent is 4

- Paper: §4, lines 455–457.
- `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.first_nonzero_central_integrable_adjoint_exponent`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/CentralFirstIntegrableSystem.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/CentralFirstIntegrableSystem.lean).
- Relevant external inputs: A03.
- Historical evidence: E01.
- Historical status: `accepted_relative_standard_SNC`.
- Scope: Actual IsLeast integrable-adjoint nonzero exponent4 already stage9 accepted, not a missing stage10 claim.

## COEFFICIENT: Uniqueness of the negative-part coefficient 1/2

- Paper: §4, lines 459–461.
- `FailureOfSemipositiveMetricExtension.negative_coefficient_unique`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean).
- `FailureOfSemipositiveMetricExtension.L_dot_ell`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean).
- `FailureOfSemipositiveMetricExtension.ell_square`
  - Snapshot E01: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Intersection.lean).
- Relevant external inputs: S06, S09.
- Historical evidence: E01, E08, E13.
- Historical status: `complete_relative_standard_Zariski_and_current_interpretations`.
- Scope: Accepted concrete divisor names, exact degrees and unique coefficient calculation, now combined with accepted independent-current residual endpoint; standard Zariski uniqueness/divisorial interpretation is explicit.

## ACK: Non-proof material

- Paper: Acknowledgments and bibliography, lines 466–536.
- No standalone Lean declaration: this is an applicability/interpretation or non-proof item.
- Relevant external inputs: none additionally itemized; shared logical foundations and geometric conventions still apply.
- Historical evidence: not a compiler-evidence item.
- Historical status: `not_evidence_not_proof_obligation`.
- Scope: Acknowledgments are not evidence; no formal mathematical task.

## Reading the boundaries correctly

- Proposition 2.1 (`prop:obstruction`) in this baseline is the integrable adjoint **extension** statement. The historical declaration name `GeneralCao.adjoint_obstruction` refers to that statement.
- Numerical identities in `Intersection.lean` are not by themselves Picard-group identities. Actual bundle cocycles, strict-transform supports and the stated classical divisor/canonical correspondences supply their geometric interpretation.
- Theorem A is assembled as a same-object analytic certificate. Standard restriction-to-disc, projectivity, algebraicity, metric/current and divisor-language bridges remain explicit. The repository does not claim a reconstruction of all of these foundational theories in Lean.
- Historical source checkpoints may use independently accepted dependencies rather than a fresh rebuild of every imported module. Read the build report for the precise reproduction scope.
- Bibliographic statements and acknowledgments are not mathematical proof evidence. No chat transcript is used as a proof or reference.
