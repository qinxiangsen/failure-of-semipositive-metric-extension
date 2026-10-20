import FailureOfSemipositiveMetricExtension.CentralCurveNormalSimple
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Identification of the actual normal tangent quotient with the actual
standard pullback of the defining divisor line. The map is induced by the true
defining-section differential, with every frame transition verified. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.CurveNormal
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

theorem tangentImage_finrank (d : Direction) : Module.finrank ℂ (tangentImage d) = 1 := by
  rw [tangentImage,tangentMap,LinearMap.finrank_range_of_inj (lineParam_mfderiv_injective d)]
  exact Module.finrank_self ℂ

theorem ambientTangent_finrank (d : Direction) : Module.finrank ℂ (AmbientTangent d) = 2 := by
  change Module.finrank ℂ (ℂ × ℂ) = 2
  simp

/-- The kernel is the actual tangent image, including at the exceptional points. -/
theorem tangentImage_eq_ker (i : Index) (d : Direction) (hi : lineParam d ∈ baseSet 0 i) :
    tangentImage d = LinearMap.ker (frameDerivative i d).toLinearMap := by
  letI : FiniteDimensional ℂ (AmbientTangent d) := inferInstanceAs (FiniteDimensional ℂ (ℂ × ℂ))
  apply Submodule.eq_of_le_of_finrank_eq (tangentImage_le_ker i d hi)
  have hdim := (frameDerivative i d).toLinearMap.finrank_range_add_finrank_ker
  have hrange : LinearMap.range (frameDerivative i d).toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr (frameDerivative_surjective i d hi)
  rw [hrange,finrank_top,Module.finrank_self,ambientTangent_finrank] at hdim
  rw [tangentImage_finrank]
  omega

/-- The actual quotient by the curve tangent has complex dimension one. -/
theorem normalFiber_finrank (d : Direction) : Module.finrank ℂ (NormalFiber d) = 1 := by
  letI : FiniteDimensional ℂ (AmbientTangent d) := inferInstanceAs (FiniteDimensional ℂ (ℂ × ℂ))
  have h := (tangentImage d).finrank_quotient_add_finrank
  rw [tangentImage_finrank,ambientTangent_finrank] at h
  change Module.finrank ℂ (AmbientTangent d ⧸ tangentImage d) = 1
  omega

/-- First isomorphism for the genuine defining-section derivative in a valid
line frame, after the proved equality of its kernel and the tangent image. -/
def frameEquiv (i : Index) (d : Direction) (hi : lineParam d ∈ baseSet 0 i) :
    NormalFiber d ≃ₗ[ℂ] ℂ :=
  (Submodule.quotEquivOfEq _ _ (tangentImage_eq_ker i d hi)).trans
    ((frameDerivative i d).toLinearMap.quotKerEquivOfSurjective (frameDerivative_surjective i d hi))

@[simp] theorem frameEquiv_mk (i : Index) (d : Direction) (hi : lineParam d ∈ baseSet 0 i)
    (v : AmbientTangent d) : frameEquiv i d hi (Submodule.Quotient.mk v) = frameDerivative i d v := rfl

/-- Normal quotient coordinates have the SAME transition direction as the
actual divisor bundle, rather than the dual/conormal transition. -/
theorem frameEquiv_transition (i j : Index) (d : Direction)
    (hi : lineParam d ∈ baseSet 0 i) (hj : lineParam d ∈ baseSet 0 j) (v : NormalFiber d) :
    frameEquiv j d hj v = gain 0 (-2) ellDegree i j (lineParam d) * frameEquiv i d hi v := by
  induction v using Submodule.Quotient.induction_on with
  | H v =>
    rw [frameEquiv_mk,frameEquiv_mk,frameDerivative_transition i j d hi hj]
    rfl

/-- The actual normal quotient identifies with the actual standard pullback
of O(ell), in its installed fibre coordinates. -/
def divisorFiberEquiv (d : Direction) :
    NormalFiber d ≃ₗ[ℂ] CurvePullback.PullbackFiber (-2) ellDegree d :=
  frameEquiv ((core 0 (-2) ellDegree).indexAt (lineParam d)) d
    ((core 0 (-2) ellDegree).mem_baseSet_at (lineParam d))

@[simp] theorem divisorFiberEquiv_mk (d : Direction) (v : AmbientTangent d) :
    divisorFiberEquiv d (Submodule.Quotient.mk v) =
      frameDerivative ((core 0 (-2) ellDegree).indexAt (lineParam d)) d v := rfl

/-- Every genuine surface line frame evaluates the same intrinsic quotient map
as its actual defining-section derivative. -/
theorem divisorFiberEquiv_localTriv (i : Index) (d : Direction)
    (hi : lineParam d ∈ baseSet 0 i) (v : NormalFiber d) :
    ((core 0 (-2) ellDegree).localTriv i ⟨lineParam d,divisorFiberEquiv d v⟩).2 =
      frameEquiv i d hi v := by
  rw [VectorBundleCore.localTriv_apply]
  exact (frameEquiv_transition ((core 0 (-2) ellDegree).indexAt (lineParam d)) i d
    ((core 0 (-2) ellDegree).mem_baseSet_at (lineParam d)) hi v).symm

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.CurveNormal
