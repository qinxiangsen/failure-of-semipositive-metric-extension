import FailureOfSemipositiveMetricExtension.FixedFiberProjectiveCertificate
import FailureOfSemipositiveMetricExtension.GlobalSubmersion
import FailureOfSemipositiveMetricExtension.GlobalPencilGeneration
import FailureOfSemipositiveMetricExtension.MetricNonextension
import FailureOfSemipositiveMetricExtension.AnalyticSingularities
import FailureOfSemipositiveMetricExtension.CentralMetricMinimality
import FailureOfSemipositiveMetricExtension.CentralCurvatureLelong
import FailureOfSemipositiveMetricExtension.CentralCurveEmbedding

/-! Same-object assembly of the analytic realization of Theorem A. All fields
refer to the original Total, projection, the actual global core (-2;1,1,1,1),
and its prescribed centralH0. The standard literature inputs already disclosed
in the imported accepted theorems remain explicit in the endpoint axiom audit.
No new axiom, algebraization predicate, or paper-specific assumption is added.
Segre/Chow/GAGA give the usual algebraic interpretation externally; their
functors and resulting algebraic realization are not fabricated in this file. -/
namespace FailureOfSemipositiveMetricExtension.PaperTheoremA
noncomputable section
open Set Topology TopologicalSpace IsManifold
open GlobalIncidence GlobalIncidence.FixedFiberBundle
open scoped Manifold ContDiff

/-- Effectivity is witnessed by an actual nonzero global analytic section of
exactly the same line bundle used by the singular metric obstruction. -/
theorem actual_global_line_effective :
    ∃ s : GlobalLineBundle.SectionData (-2) (fun _ => 1),
      ∃ p : Total, GlobalLineBundle.sectionValue s p ≠ 0 := by
  let p := FixedFiber.inclusion 1 (FixedFiber.BlowdownComplement.lift 1 (centre 0 1))
  have hp : projection p ≠ 0 := by change (1 : ℂ) ≠ 0; norm_num
  obtain ⟨k,hk⟩ := GlobalLineBundle.liftedPencil_no_basepoint p hp
  exact ⟨GlobalLineBundle.liftedPencil k,p,hk⟩

/-- Effectivity survives restriction to every disc around zero: every nonzero
parameter already has a nonzero value of a genuine global section. -/
theorem actual_global_line_effective_at_nonzero_parameter (t : ℂ) (ht : t ≠ 0) :
    ∃ s : GlobalLineBundle.SectionData (-2) (fun _ => 1),
      ∃ p : Fiber t, GlobalLineBundle.sectionValue s (FixedFiber.inclusion t p) ≠ 0 := by
  let p := FixedFiber.BlowdownComplement.lift t (centre 0 t)
  obtain ⟨k,hk⟩ := GlobalLineBundle.liftedPencil_no_basepoint (FixedFiber.inclusion t p) ht
  exact ⟨GlobalLineBundle.liftedPencil k,p,hk⟩

/-- A concrete statement, not an opaque label for projectivity or rationality.
These are the actual geometric inputs for standard algebraic interpretation. -/
def ProjectiveRationalFiberInputs (t : ℂ) : Prop :=
  CompactSpace (Fiber t) ∧ IsManifold 𝓘(ℂ,FixedFiber.Coord) ω (Fiber t) ∧
    IsClosedEmbedding (FixedFiber.projectiveInclusion t) ∧
    ContMDiff 𝓘(ℂ,FixedFiber.Coord) FixedFiber.projectiveAmbientModel ω
      (FixedFiber.projectiveInclusion t) ∧
    (∀ p : Fiber t, Function.Injective
      (mfderiv 𝓘(ℂ,FixedFiber.Coord) FixedFiber.projectiveAmbientModel
        (FixedFiber.projectiveInclusion t) p)) ∧
    IsProperMap (FixedFiber.blowdown t) ∧ Function.Surjective (FixedFiber.blowdown t) ∧
    Dense (FixedFiber.BlowdownComplement.partialHomeomorph t).source ∧
    Dense (FixedFiber.BlowdownComplement.partialHomeomorph t).target ∧
    ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ,ℂ × ℂ) ω
      (FixedFiber.BlowdownComplement.partialHomeomorph t)
      (FixedFiber.BlowdownComplement.partialHomeomorph t).source ∧
    ContMDiffOn 𝓘(ℂ,ℂ × ℂ) 𝓘(ℂ,FixedFiber.Coord) ω
      (FixedFiber.BlowdownComplement.partialHomeomorph t).symm
      (FixedFiber.BlowdownComplement.partialHomeomorph t).target

/-- Every component refers to one specified family, one specified global line,
one specified h0 and its actual zero-locus curve. There are no interchangeable
existentially chosen surfaces, metrics, or line bundles between these fields. -/
structure AnalyticCounterexampleCertificate : Prop where
  proper_submersion : IsProperMap projection ∧
    ContMDiff 𝓘(ℂ,ChartCoord) 𝓘(ℂ) ω projection ∧ IsOpenMap projection ∧
    ∀ p : Total, Function.Surjective (mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ) projection p)
  relative_projective_embedding : IsClosedEmbedding (fun p : Total => p.val) ∧
    ContMDiff 𝓘(ℂ,ChartCoord) ambientModel ω (fun p : Total => p.val) ∧
    ∀ p : Total, Function.Injective
      (mfderiv 𝓘(ℂ,ChartCoord) ambientModel (fun q : Total => q.val) p)
  projective_rational_fiber_inputs : ∀ t : ℂ, ProjectiveRationalFiberInputs t
  effective_line : ∃ s : GlobalLineBundle.SectionData (-2) (fun _ => 1),
    ∃ p : Total, GlobalLineBundle.sectionValue s p ≠ 0
  effective_on_nonzero_fibers : ∀ (t : ℂ), t ≠ 0 →
    ∃ s : GlobalLineBundle.SectionData (-2) (fun _ => 1),
      ∃ p : Fiber t, GlobalLineBundle.sectionValue s (FixedFiber.inclusion t p) ≠ 0
  semipositive_central_metric : HasPlurisubharmonicWeights centralH0
  analytic_singularities : HasAnalyticSingularities centralH0
  minimal_singularities : HasMinimalSingularities centralH0
  exact_singular_support : ∀ (i : Index) (p : Fiber 0), p ∈ baseSet 0 i →
    (centralH0.weight i p = ⊥ ↔ sectionValue ellSection p = 0)
  embedded_curve : CompactSpace EllCurve ∧ IsManifold 𝓘(ℂ) ω EllCurve ∧
    IsClosedEmbedding (fun p : EllCurve => p.val) ∧
    ContMDiff 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) ω (fun p : EllCurve => p.val) ∧
    ∀ p : EllCurve, Function.Injective
      (mfderiv 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) (fun q : EllCurve => q.val) p)
  rational_curve : ∃ e : Direction ≃ₜ EllCurve,
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω e ∧ ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω e.symm
  lelong_half : ∀ (p : Fiber 0), sectionValue ellSection p = 0 →
    ∃ d : DivisionIndex, p ∈ divisionPatch 0 d ∧
      ∃ T : PshCurvatureCurrentInterface.CurvatureCurrent
        (fun q => centralH0.weight (divisionFrame d) (FixedFiber.param 0 d.1 d.2.1 q))
        (weightChartDomain 0 (divisionFrame d) d.1 d.2.1),
        PshCurvatureCurrentInterface.HasLelongNumber T
          (FixedFiber.coordinates 0 d.1 d.2.1 p) (1/2)
  one_sided_nonextension : ∀ (U : Opens Total), GlobalLineBundle.ContainsCentralFiber U →
    ¬ ∃ h : GlobalLineBundle.SingularWeightOn U (-2) (fun _ => 1),
      h.HasPlurisubharmonicWeights ∧ h.centralDominatesH0
  exact_nonextension : ∀ (U : Opens Total), GlobalLineBundle.ContainsCentralFiber U →
    ¬ ∃ h : GlobalLineBundle.SingularWeightOn U (-2) (fun _ => 1),
      h.HasPlurisubharmonicWeights ∧ h.centralExactH0
  same_singularity_nonextension : ∀ (U : Opens Total), GlobalLineBundle.ContainsCentralFiber U →
    ¬ ∃ h : GlobalLineBundle.SingularWeightOn U (-2) (fun _ => 1),
      h.HasPlurisubharmonicWeights ∧ h.centralSameBoundedSingularityType

/-- The complete same-object analytic theorem-A certificate, with the existing
standard literature inputs retained and no new mathematical assumptions. -/
theorem actual_analytic_counterexample : AnalyticCounterexampleCertificate where
  proper_submersion := proper_analytic_submersion
  relative_projective_embedding := total_analytic_closed_immersion
  projective_rational_fiber_inputs := FixedFiber.actual_fiber_projective_rational_input_certificate
  effective_line := actual_global_line_effective
  effective_on_nonzero_fibers := actual_global_line_effective_at_nonzero_parameter
  semipositive_central_metric := centralH0_plurisubharmonic
  analytic_singularities := centralH0_analytic_singularities
  minimal_singularities := centralH0_hasMinimalSingularities
  exact_singular_support := centralH0_eq_bot_iff
  embedded_curve := ellCurve_compact_analytic_embedded
  rational_curve := ellCurve_biholomorphic
  lelong_half := centralH0_current_lelong_half
  one_sided_nonextension := GlobalLineBundle.no_semipositive_metric_dominating_centralH0
  exact_nonextension := GlobalLineBundle.no_exact_semipositive_extension
  same_singularity_nonextension := GlobalLineBundle.no_semipositive_extension_same_bounded_singularity_type

end
end FailureOfSemipositiveMetricExtension.PaperTheoremA
