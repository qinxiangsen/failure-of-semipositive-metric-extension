import FailureOfSemipositiveMetricExtension.ComplexSurfaceJacobian
import Mathlib.LinearAlgebra.Basis.Prod

/-! Actual three-dimensional complex determinants and the ordered volume form,
with the fibre coordinates first and the family parameter last. -/
namespace FailureOfSemipositiveMetricExtension.ComplexThreefoldJacobian
noncomputable section
open Set
open scoped Manifold ContDiff

abbrev Coord := (ℂ × ℂ) × ℂ

def coordinateBasis : Basis (Fin 3) ℂ Coord :=
  ((Basis.finTwoProd ℂ).prod (Basis.singleton (Fin 1) ℂ)).reindex finSumFinEquiv

def coordinateVolume : Coord [⋀^Fin 3]→ₗ[ℂ] ℂ := coordinateBasis.det

def determinant (A : Coord →L[ℂ] Coord) : ℂ := LinearMap.det A.toLinearMap

theorem determinant_formula (A : Coord →L[ℂ] Coord) :
    determinant A =
      (A ((1,0),0)).1.1 * (A ((0,1),0)).1.2 * (A ((0,0),1)).2 +
      (A ((0,1),0)).1.1 * (A ((0,0),1)).1.2 * (A ((1,0),0)).2 +
      (A ((0,0),1)).1.1 * (A ((1,0),0)).1.2 * (A ((0,1),0)).2 -
      (A ((0,0),1)).1.1 * (A ((0,1),0)).1.2 * (A ((1,0),0)).2 -
      (A ((0,1),0)).1.1 * (A ((1,0),0)).1.2 * (A ((0,0),1)).2 -
      (A ((1,0),0)).1.1 * (A ((0,0),1)).1.2 * (A ((0,1),0)).2 := by
  rw [determinant,← LinearMap.det_toMatrix coordinateBasis,Matrix.det_fin_three]
  have h0 : finSumFinEquiv.symm (0 : Fin 3) = (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 1) := rfl
  have h1 : finSumFinEquiv.symm (1 : Fin 3) = (Sum.inl (1 : Fin 2) : Fin 2 ⊕ Fin 1) := rfl
  have h2 : finSumFinEquiv.symm (2 : Fin 3) = (Sum.inr (0 : Fin 1) : Fin 2 ⊕ Fin 1) := rfl
  simp [LinearMap.toMatrix_apply,coordinateBasis,Basis.coe_finTwoProd_repr,h0,h1,h2]
  <;> ring

def jacobian (f : Coord → Coord) (q : Coord) : ℂ := determinant (fderiv ℂ f q)

theorem jacobian_comp {f g : Coord → Coord} (q : Coord)
    (hf : DifferentiableAt ℂ f q) (hg : DifferentiableAt ℂ g (f q)) :
    jacobian (g ∘ f) q = jacobian g (f q) * jacobian f q := by
  rw [jacobian,fderiv_comp q hg hf]
  exact LinearMap.det_comp _ _

@[simp] theorem jacobian_id (q : Coord) : jacobian id q = 1 := by
  simp [jacobian,determinant]

theorem determinant_contDiff (n : WithTop ℕ∞) : ContDiff ℂ n determinant := by
  rw [show determinant = _ from funext determinant_formula]
  have he (v : Coord) : ContDiff ℂ n (fun A : Coord →L[ℂ] Coord => A v) :=
    (ContinuousLinearMap.apply ℂ Coord v).contDiff
  have h1 := ((he ((1,0),0)).fst.fst.mul (he ((0,1),0)).fst.snd).mul (he ((0,0),1)).snd
  have h2 := ((he ((0,1),0)).fst.fst.mul (he ((0,0),1)).fst.snd).mul (he ((1,0),0)).snd
  have h3 := ((he ((0,0),1)).fst.fst.mul (he ((1,0),0)).fst.snd).mul (he ((0,1),0)).snd
  have h4 := ((he ((0,0),1)).fst.fst.mul (he ((0,1),0)).fst.snd).mul (he ((1,0),0)).snd
  have h5 := ((he ((0,1),0)).fst.fst.mul (he ((1,0),0)).fst.snd).mul (he ((0,0),1)).snd
  have h6 := ((he ((1,0),0)).fst.fst.mul (he ((0,0),1)).fst.snd).mul (he ((0,1),0)).snd
  exact ((((h1.add h2).add h3).sub h4).sub h5).sub h6

theorem jacobian_contDiffOn {f : Coord → Coord} {U : Set Coord}
    (hf : ContDiffOn ℂ ω f U) (hU : IsOpen U) :
    ContDiffOn ℂ ω (jacobian f) U :=
  (determinant_contDiff ω).comp_contDiffOn (hf.fderiv_of_isOpen hU (by simp))

/-- A parameter-preserving linear map has the same determinant as its vertical
restriction. This is the exact algebraic orientation used by dt adjunction. -/
theorem determinant_parameter_preserving (A : Coord →L[ℂ] Coord)
    (hA : ∀ q, (A q).2 = q.2) :
    determinant A = ComplexSurfaceJacobian.determinant
      ((ContinuousLinearMap.fst ℂ (ℂ × ℂ) ℂ).comp (A.comp (ContinuousLinearMap.inl ℂ (ℂ × ℂ) ℂ))) := by
  rw [determinant_formula,ComplexSurfaceJacobian.determinant_formula]
  simp [hA]

end
end FailureOfSemipositiveMetricExtension.ComplexThreefoldJacobian
