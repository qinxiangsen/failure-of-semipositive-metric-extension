import FailureOfSemipositiveMetricExtension.CentralSingularRegularity
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Exact cancellation and regularity of the central section's fourth-power
weighted local density. Canonical-bundle identification is still separate. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold MeasureTheory
open scoped Manifold ContDiff

def sigmaWeightedDensity (i : Index) (p : Fiber 0) : ℝ :=
  Complex.normSq (sigmaSection.coefficient i p) * Real.exp (-4 * centralH0RealWeight i p)

def sigmaRegularDensity (i : Index) (p : Fiber 0) : ℝ :=
  Complex.normSq (qSection.coefficient i p) / (sectionNormSum liftedCentralCubics i p)^2

/-- The prescribed factor ell² cancels the fourth tensor-power singularity exactly. -/
theorem sigmaWeightedDensity_eq_regular (i : Index) (p : Fiber 0)
    (hp : p ∈ baseSet 0 i) (he : ellSection.coefficient i p ≠ 0) :
    sigmaWeightedDensity i p = sigmaRegularDensity i p := by
  have hS := sectionNormSum_positive liftedCentralCubics liftedCentralCubics_basepoint_free i p hp
  have hE := Complex.normSq_pos.mpr he
  have hexp : -4 * centralH0RealWeight i p =
      -(Real.log (sectionNormSum liftedCentralCubics i p) +
        Real.log (sectionNormSum liftedCentralCubics i p)) +
      -(Real.log (Complex.normSq (ellSection.coefficient i p)) +
        Real.log (Complex.normSq (ellSection.coefficient i p))) := by
    unfold centralH0RealWeight
    ring
  unfold sigmaWeightedDensity sigmaRegularDensity
  rw [sigmaSection_coefficient,Complex.normSq_mul,map_pow,hexp,Real.exp_add,
    Real.exp_neg,Real.exp_neg,Real.exp_add,Real.exp_add,Real.exp_log hS,Real.exp_log hE]
  field_simp
  ring

/-- The canceled density is real analytic across ell in every actual frame. -/
theorem sigmaRegularDensity_contMDiffOn (i : Index) :
    ContMDiffOn 𝓘(ℝ,FixedFiber.Coord) 𝓘(ℝ) ω (sigmaRegularDensity i) (baseSet 0 i) := by
  have hQ := (FailureOfSemipositiveMetricExtension.normSq_contDiff_real ω).contMDiff.comp_contMDiffOn
    (FailureOfSemipositiveMetricExtension.complex_contMDiffOn_real (qSection.analytic i))
  have hS := sectionNormSum_contMDiffOn liftedCentralCubics i
  have hi : ContDiffOn ℝ ω (fun x : ℝ => x⁻¹) {x | x ≠ 0} :=
    contDiffOn_id.inv (fun _ h => h)
  have hI := hi.contMDiffOn.comp (hS.smul hS) (fun p hp =>
    mul_ne_zero (ne_of_gt (sectionNormSum_positive liftedCentralCubics liftedCentralCubics_basepoint_free i p hp))
      (ne_of_gt (sectionNormSum_positive liftedCentralCubics liftedCentralCubics_basepoint_free i p hp)))
  change ContMDiffOn 𝓘(ℝ,FixedFiber.Coord) 𝓘(ℝ) ω (fun p => Complex.normSq (qSection.coefficient i p) / (sectionNormSum liftedCentralCubics i p)^2) (baseSet 0 i)
  simpa only [pow_two,div_eq_mul_inv,smul_eq_mul,Function.comp_apply] using hQ.smul hI

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
