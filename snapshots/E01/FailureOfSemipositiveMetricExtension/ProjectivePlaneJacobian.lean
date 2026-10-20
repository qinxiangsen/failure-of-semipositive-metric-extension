import FailureOfSemipositiveMetricExtension.ComplexSurfaceJacobian
import FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle

/-! The actual nine projective-plane chart changes have the signed cubic
Jacobian law.  The signs fix the alternating ordering of the two affine coordinates. -/
namespace FailureOfSemipositiveMetricExtension.ComplexSurfaceJacobian
noncomputable section
open Set


def reciprocal (q : Coord) : Coord := (q.1⁻¹,q.2/q.1)

def reciprocalDerivative (q : Coord) : Coord →L[ℂ] Coord :=
  (-(q.1 ^ 2)⁻¹ • ContinuousLinearMap.fst ℂ ℂ ℂ).prod
    (q.2 • (-(q.1 ^ 2)⁻¹ • ContinuousLinearMap.fst ℂ ℂ ℂ) +
      q.1⁻¹ • ContinuousLinearMap.snd ℂ ℂ ℂ)

theorem reciprocal_hasFDerivAt (q : Coord) (hq : q.1 ≠ 0) :
    HasFDerivAt reciprocal (reciprocalDerivative q) q := by
  have hi := (hasDerivAt_inv hq).comp_hasFDerivAt q (hasFDerivAt_fst (𝕜 := ℂ))
  simpa only [reciprocal,div_eq_mul_inv] using hi.prodMk (hasFDerivAt_snd.mul hi)

theorem reciprocal_jacobian (q : Coord) (hq : q.1 ≠ 0) :
    jacobian reciprocal q = -(q.1 ^ 3)⁻¹ := by
  rw [jacobian,(reciprocal_hasFDerivAt q hq).fderiv,determinant_formula]
  simp [reciprocalDerivative]
  field_simp
  <;> ring

theorem swap_hasFDerivAt (q : Coord) : HasFDerivAt Prod.swap
    ((ContinuousLinearMap.snd ℂ ℂ ℂ).prod (ContinuousLinearMap.fst ℂ ℂ ℂ)) q :=
  hasFDerivAt_snd.prodMk hasFDerivAt_fst

@[simp] theorem swap_jacobian (q : Coord) : jacobian Prod.swap q = -1 := by
  rw [jacobian,(swap_hasFDerivAt q).fderiv,determinant_formula]
  norm_num

theorem reciprocal_swap_jacobian (q : Coord) (hq : q.2 ≠ 0) :
    jacobian (reciprocal ∘ Prod.swap) q = (q.2 ^ 3)⁻¹ := by
  rw [jacobian_comp q (swap_hasFDerivAt q).differentiableAt
    (reciprocal_hasFDerivAt q.swap hq).differentiableAt,reciprocal_jacobian q.swap hq,swap_jacobian]
  simp

theorem swap_reciprocal_jacobian (q : Coord) (hq : q.1 ≠ 0) :
    jacobian (Prod.swap ∘ reciprocal) q = (q.1 ^ 3)⁻¹ := by
  rw [jacobian_comp q (reciprocal_hasFDerivAt q hq).differentiableAt
    (swap_hasFDerivAt _).differentiableAt,swap_jacobian,reciprocal_jacobian q hq]
  simp

theorem swap_reciprocal_swap_jacobian (q : Coord) (hq : q.2 ≠ 0) :
    jacobian (Prod.swap ∘ (reciprocal ∘ Prod.swap)) q = -(q.2 ^ 3)⁻¹ := by
  rw [jacobian_comp q
    ((reciprocal_hasFDerivAt q.swap hq).comp q (swap_hasFDerivAt q)).differentiableAt
    (swap_hasFDerivAt _).differentiableAt,swap_jacobian,reciprocal_swap_jacobian q hq]
  simp

def planeSign (i : Fin 3) : ℂ := if i = 1 then -1 else 1

/-- The actual rational projective-plane transition has the precise determinant. -/
theorem plane_transition_jacobian (i j : Fin 3) (q : Coord)
    (hq : q ∈ ProjectivePlane.overlap i j) :
    jacobian (ProjectivePlane.transition i j) q =
      planeSign i * planeSign j * (ProjectivePlane.vector i q j ^ 3)⁻¹ := by
  fin_cases i <;> fin_cases j
  · change jacobian id q = _
    simp [planeSign,ProjectivePlane.vector]
  · exact (reciprocal_jacobian q hq).trans (by simp [planeSign,ProjectivePlane.vector])
  · exact (reciprocal_swap_jacobian q hq).trans (by simp [planeSign,ProjectivePlane.vector])
  · exact (reciprocal_jacobian q hq).trans (by simp [planeSign,ProjectivePlane.vector])
  · change jacobian id q = _
    simp [planeSign,ProjectivePlane.vector]
  · exact (swap_reciprocal_swap_jacobian q hq).trans (by simp [planeSign,ProjectivePlane.vector])
  · exact (swap_reciprocal_jacobian q hq).trans (by simp [planeSign,ProjectivePlane.vector])
  · exact (swap_reciprocal_swap_jacobian q hq).trans (by simp [planeSign,ProjectivePlane.vector])
  · change jacobian id q = _
    simp [planeSign,ProjectivePlane.vector]

end
end FailureOfSemipositiveMetricExtension.ComplexSurfaceJacobian
