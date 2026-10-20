import FailureOfSemipositiveMetricExtension.FixedFiberCanonicalTransition

/-! Explicit nonzero alternating coordinate two-forms and their genuine derivative
pullback law.  This supplies the two-form semantics of the Jacobian cocycle. -/
namespace FailureOfSemipositiveMetricExtension.ComplexSurfaceJacobian
noncomputable section

def coordinateVolume : Coord [⋀^Fin 2]→ₗ[ℂ] ℂ := (Basis.finTwoProd ℂ).det

@[simp] theorem coordinateVolume_basis : coordinateVolume (Basis.finTwoProd ℂ) = 1 :=
  Basis.det_self _

theorem coordinateVolume_comp (A : Coord →L[ℂ] Coord) :
    coordinateVolume.compLinearMap A.toLinearMap = determinant A • coordinateVolume := by
  ext v
  exact Basis.det_comp (Basis.finTwoProd ℂ) A.toLinearMap v

theorem coordinateVolume_ne_zero : coordinateVolume ≠ 0 := by
  intro h
  have he := congrArg (fun f : Coord [⋀^Fin 2]→ₗ[ℂ] ℂ => f (Basis.finTwoProd ℂ)) h
  simpa using he

end
end FailureOfSemipositiveMetricExtension.ComplexSurfaceJacobian

namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set ComplexSurfaceJacobian

/-- A genuine alternating complex two-form in each of the verified coordinate frames. -/
def localCanonicalForm (t : ℂ) (d : DivisionIndex) (p : Fiber t) :
    FixedFiber.Coord [⋀^Fin 2]→ₗ[ℂ] ℂ := canonicalFactor t d p • coordinateVolume

theorem localCanonicalForm_ne_zero (t : ℂ) (d : DivisionIndex) (p : Fiber t)
    (hp : p ∈ divisionPatch t d) : localCanonicalForm t d p ≠ 0 := by
  intro hz
  have h := congrArg (fun f : FixedFiber.Coord [⋀^Fin 2]→ₗ[ℂ] ℂ => f (Basis.finTwoProd ℂ)) hz
  have hc : canonicalFactor t d p = 0 := by simpa [localCanonicalForm] using h
  exact canonicalFactor_ne_zero t d p hp hc

/-- Pullback by the actual complex derivative gives precisely the ambient K transition. -/
theorem localCanonicalForm_pullback (t : ℂ) (d c : DivisionIndex) (p : Fiber t)
    (hd : p ∈ divisionPatch t d) (hc : p ∈ divisionPatch t c) :
    gain t 1 (fun _ => -1) (divisionFrame d) (divisionFrame c) p •
      ((localCanonicalForm t c p).compLinearMap
        (fderiv ℂ (FixedFiber.change t d.1 c.1 d.2.1 c.2.1)
          (FixedFiber.coordinates t d.1 d.2.1 p)).toLinearMap) = localCanonicalForm t d p := by
  ext v
  change gain t 1 (fun _ => -1) (divisionFrame d) (divisionFrame c) p *
    (canonicalFactor t c p * coordinateVolume
      ((fderiv ℂ (FixedFiber.change t d.1 c.1 d.2.1 c.2.1)
        (FixedFiber.coordinates t d.1 d.2.1 p)).toLinearMap ∘ v)) = canonicalFactor t d p * coordinateVolume v
  dsimp only [coordinateVolume]
  rw [Basis.det_comp]
  change _ * (_ * (FixedFiber.chartJacobian t d.1 c.1 d.2.1 c.2.1 p * coordinateVolume v)) = _
  rw [← mul_assoc,← mul_assoc,canonicalFactor_jacobian t d c p hd hc]
  rfl

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
