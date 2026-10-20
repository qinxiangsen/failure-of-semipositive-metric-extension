import FailureOfSemipositiveMetricExtension.GlobalFiberManifold
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Basis.Fin

/-! Genuine complex Jacobian determinants on affine two-space, including the
local blow-up projection and its actual rational chart change. -/
namespace FailureOfSemipositiveMetricExtension.ComplexSurfaceJacobian
noncomputable section
open Set
open scoped Manifold ContDiff

abbrev Coord := ℂ × ℂ

def determinant (A : Coord →L[ℂ] Coord) : ℂ := LinearMap.det A.toLinearMap

theorem determinant_formula (A : Coord →L[ℂ] Coord) :
    determinant A = (A (1,0)).1 * (A (0,1)).2 - (A (0,1)).1 * (A (1,0)).2 := by
  rw [determinant,← LinearMap.det_toMatrix (Basis.finTwoProd ℂ),Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply,Basis.coe_finTwoProd_repr]

def jacobian (f : Coord → Coord) (q : Coord) : ℂ := determinant (fderiv ℂ f q)

theorem jacobian_comp {f g : Coord → Coord} (q : Coord)
    (hf : DifferentiableAt ℂ f q) (hg : DifferentiableAt ℂ g (f q)) :
    jacobian (g ∘ f) q = jacobian g (f q) * jacobian f q := by
  rw [jacobian,fderiv_comp q hg hf]
  exact LinearMap.det_comp _ _

@[simp] theorem jacobian_id (q : Coord) : jacobian id q = 1 := by
  simp [jacobian,determinant]

/-- The two actual affine blow-down polynomials. -/
def blowdown : Fin 2 → Coord → Coord
  | 0,q => (q.1,q.1*q.2)
  | 1,q => (q.1*q.2,q.1)

def blowdownDerivative : Fin 2 → Coord → (Coord →L[ℂ] Coord)
  | 0,q => (ContinuousLinearMap.fst ℂ ℂ ℂ).prod
      (q.1 • ContinuousLinearMap.snd ℂ ℂ ℂ + q.2 • ContinuousLinearMap.fst ℂ ℂ ℂ)
  | 1,q => (q.1 • ContinuousLinearMap.snd ℂ ℂ ℂ + q.2 • ContinuousLinearMap.fst ℂ ℂ ℂ).prod
      (ContinuousLinearMap.fst ℂ ℂ ℂ)

theorem blowdown_hasFDerivAt (e : Fin 2) (q : Coord) :
    HasFDerivAt (blowdown e) (blowdownDerivative e q) q := by
  fin_cases e
  · exact hasFDerivAt_fst.prodMk (hasFDerivAt_fst.mul hasFDerivAt_snd)
  · exact (hasFDerivAt_fst.mul hasFDerivAt_snd).prodMk hasFDerivAt_fst

def directionSign (e : Fin 2) : ℂ := if e = 0 then 1 else -1

theorem blowdown_jacobian (e : Fin 2) (q : Coord) :
    jacobian (blowdown e) q = directionSign e * q.1 := by
  rw [jacobian,(blowdown_hasFDerivAt e q).fderiv,determinant_formula]
  fin_cases e <;> simp [blowdownDerivative,directionSign]

def transitionDerivative (q : Coord) : Coord →L[ℂ] Coord :=
  (q.1 • ContinuousLinearMap.snd ℂ ℂ ℂ + q.2 • ContinuousLinearMap.fst ℂ ℂ ℂ).prod
    (-(q.2 ^ 2)⁻¹ • ContinuousLinearMap.snd ℂ ℂ ℂ)

theorem transition_hasFDerivAt (q : Coord) (hq : q.2 ≠ 0) :
    HasFDerivAt Blowup.transition (transitionDerivative q) q := by
  have hi := (hasDerivAt_inv hq).comp_hasFDerivAt q (hasFDerivAt_snd (𝕜 := ℂ))
  exact (hasFDerivAt_fst.mul hasFDerivAt_snd).prodMk hi

/-- The genuine X-to-Y (and Y-to-X) chart change has determinant -1/s. -/
theorem transition_jacobian (q : Coord) (hq : q.2 ≠ 0) :
    jacobian Blowup.transition q = -q.2⁻¹ := by
  rw [jacobian,(transition_hasFDerivAt q hq).fderiv,determinant_formula]
  simp only [transitionDerivative,ContinuousLinearMap.prod_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.coe_fst,ContinuousLinearMap.coe_snd,
    smul_eq_mul,mul_zero,mul_one,add_zero,zero_add,sub_zero]
  field_simp
  <;> ring

theorem determinant_contDiff (n : WithTop ℕ∞) : ContDiff ℂ n determinant := by
  have h : determinant = fun A : Coord →L[ℂ] Coord =>
      (A (1,0)).1 * (A (0,1)).2 - (A (0,1)).1 * (A (1,0)).2 := funext determinant_formula
  rw [h]
  have he (v : Coord) : ContDiff ℂ n (fun A : Coord →L[ℂ] Coord => A v) :=
    (ContinuousLinearMap.apply ℂ Coord v).contDiff
  exact ((he (1,0)).fst.mul (he (0,1)).snd).sub ((he (0,1)).fst.mul (he (1,0)).snd)

theorem jacobian_contDiffOn {f : Coord → Coord} {U : Set Coord}
    (hf : ContDiffOn ℂ ω f U) (hU : IsOpen U) :
    ContDiffOn ℂ ω (jacobian f) U :=
  (determinant_contDiff ω).comp_contDiffOn (hf.fderiv_of_isOpen hU (by simp))

@[simp] theorem directionSign_mul_self (e : Fin 2) : directionSign e * directionSign e = 1 := by
  fin_cases e <;> norm_num [directionSign]

theorem directionSign_ne_zero (e : Fin 2) : directionSign e ≠ 0 := by
  fin_cases e <;> norm_num [directionSign]

end
end FailureOfSemipositiveMetricExtension.ComplexSurfaceJacobian
