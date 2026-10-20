import FailureOfSemipositiveMetricExtension.CentralQLocalSimple
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! The explicit transverse derivatives give a genuine surjective complex
Fréchet derivative at every zero of Q's actual local equation. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section

def qTransverseTangent (r : Fin 4) (e : Fin 2) : FixedFiber.Coord :=
  if r ≠ 3 ∧ e = 0 then (1,0) else (0,1)

theorem qTransversePath_hasDerivAt (r : Fin 4) (e : Fin 2) (q : FixedFiber.Coord) :
    HasDerivAt (qTransversePath r e q) (qTransverseTangent r e)
      (qTransverseParameter r e q) := by
  unfold qTransversePath qTransverseTangent qTransverseParameter
  split_ifs
  · exact (hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2)
  · exact (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)

theorem qLocalCoefficient_fderiv_transverse (r : Fin 4) (e : Fin 2) (q : FixedFiber.Coord) :
    fderiv ℂ (qLocalCoefficient r e) q (qTransverseTangent r e) = qTransverseDerivative r e q := by
  have hd : DifferentiableAt ℂ (qLocalCoefficient r e) q :=
    ((qLocalCoefficient_contDiff r e).differentiable (by decide)).differentiableAt
  have hchain := hd.hasFDerivAt.comp_hasDerivAt_of_eq (qTransverseParameter r e q)
    (qTransversePath_hasDerivAt r e q) (qTransversePath_at_parameter r e q).symm
  exact hchain.unique (qLocalCoefficient_transverse_hasDerivAt r e q)

/-- This is surjectivity of the actual continuous complex-linear derivative,
with an explicit preimage for every target complex number. -/
theorem qLocalCoefficient_fderiv_surjective_at_zero (r : Fin 4) (e : Fin 2)
    (q : FixedFiber.Coord) (hq : qLocalCoefficient r e q = 0) :
    Function.Surjective (fderiv ℂ (qLocalCoefficient r e) q) := by
  intro z
  refine ⟨(z / qTransverseDerivative r e q) • qTransverseTangent r e,?_⟩
  rw [map_smul,qLocalCoefficient_fderiv_transverse,smul_eq_mul]
  exact div_mul_cancel₀ _ (qTransverseDerivative_ne_zero_at_zero r e q hq)

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
