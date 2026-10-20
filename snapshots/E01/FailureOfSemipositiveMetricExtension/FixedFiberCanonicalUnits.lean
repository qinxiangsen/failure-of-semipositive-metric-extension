import FailureOfSemipositiveMetricExtension.FixedFiberCanonicalTangentForms

/-! Exact local analytic-unit comparison between the original sigma coefficients
and the coefficients of its genuine canonical-times-L-fourth section. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold
open scoped Manifold ContDiff

theorem canonicalFactor_inv_contMDiffOn (t : ℂ) (d : DivisionIndex) :
    ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω
      (fun p => (canonicalFactor t d p)⁻¹) (divisionPatch t d) := by
  have h : ContDiffOn ℂ ω (fun z : ℂ => z⁻¹) {z | z ≠ 0} := contDiffOn_id.inv (fun _ h => h)
  exact h.contMDiffOn.comp (canonicalFactor_contMDiffOn t d)
    (fun p hp => canonicalFactor_ne_zero t d p hp)

theorem canonicalFactor_isUnit (t : ℂ) (d : DivisionIndex) (p : Fiber t)
    (hp : p ∈ divisionPatch t d) : IsUnit (canonicalFactor t d p) :=
  isUnit_iff_ne_zero.mpr (canonicalFactor_ne_zero t d p hp)

theorem sigmaAdjointCoefficient_eq (d : DivisionIndex) (p : Fiber 0) :
    sigmaAdjointCoefficient d p = canonicalFactor 0 d p * sigmaSection.coefficient (divisionFrame d) p := rfl

theorem sigmaCoefficient_of_adjoint (d : DivisionIndex) (p : Fiber 0)
    (hp : p ∈ divisionPatch 0 d) :
    sigmaSection.coefficient (divisionFrame d) p =
      (canonicalFactor 0 d p)⁻¹ * sigmaAdjointCoefficient d p := by
  rw [sigmaAdjointCoefficient,← mul_assoc,inv_mul_cancel₀ (canonicalFactor_ne_zero 0 d p hp),one_mul]

theorem sigmaAdjointCoefficient_zero_iff (d : DivisionIndex) (p : Fiber 0)
    (hp : p ∈ divisionPatch 0 d) :
    sigmaAdjointCoefficient d p = 0 ↔ sigmaSection.coefficient (divisionFrame d) p = 0 := by
  simp only [sigmaAdjointCoefficient,mul_eq_zero,canonicalFactor_ne_zero 0 d p hp,false_or]

theorem sigmaAdjointCoefficient_normSq (d : DivisionIndex) (p : Fiber 0) :
    Complex.normSq (sigmaAdjointCoefficient d p) =
      Complex.normSq (canonicalFactor 0 d p) *
        Complex.normSq (sigmaSection.coefficient (divisionFrame d) p) :=
  Complex.normSq_mul _ _

theorem canonicalFactor_normSq_pos (t : ℂ) (d : DivisionIndex) (p : Fiber t)
    (hp : p ∈ divisionPatch t d) : 0 < Complex.normSq (canonicalFactor t d p) := by
  exact Complex.normSq_pos.mpr (canonicalFactor_ne_zero t d p hp)

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
