import FailureOfSemipositiveMetricExtension.CanonicalAdjunctionForms

/-! The actual dt-contraction map is an isomorphism of the full cotangent
 determinant fibres, with an explicit inverse and no normal-vector choice. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalCanonical
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

/-- The inverse wedges a fibre top form with dt; its coordinate expression is
independent of horizontal terms, by the previously proved contraction theorem. -/
def adjunctionEquiv (t : ℂ) (p : Fiber t) :
    CanonicalTangentFiber (FixedFiber.inclusion t p) ≃ₗ[ℂ] FixedFiber.CanonicalTangentFiber t p := by
  let i := (FixedFiber.canonicalCore t).indexAt p
  have hp : p ∈ FixedFiber.source t i.1 i.2 := (FixedFiber.canonicalCore t).mem_baseSet_at p
  let B := FixedFiber.tangentBasis t i.1 i.2 p hp
  let C := tangentBasis i.1 i.2 (FixedFiber.inclusion t p) hp
  have hmap : adjunction t p C.det = B.det := by
    rw [← tangentCoordinateForm_eq_basis_det i.1 i.2 (FixedFiber.inclusion t p) hp,
      ← FixedFiber.tangentCoordinateForm_eq_basis_det t i.1 i.2 p hp]
    exact adjunction_coordinateForm t i.1 i.2 p hp
  exact
    { toLinearMap := adjunction t p
      invFun := fun f => f B • C.det
      left_inv := fun f => by
        change (adjunction t p f) B • C.det = f
        have hf := f.eq_smul_basis_det C
        conv_lhs => rw [hf]
        rw [map_smul,hmap]
        simp only [AlternatingMap.smul_apply,Basis.det_self,smul_eq_mul,mul_one]
        exact hf.symm
      right_inv := fun f => by
        change adjunction t p (f B • C.det) = f
        rw [map_smul,hmap]
        exact (f.eq_smul_basis_det B).symm }

@[simp] theorem adjunctionEquiv_apply (t : ℂ) (p : Fiber t)
    (f : CanonicalTangentFiber (FixedFiber.inclusion t p)) :
    adjunctionEquiv t p f = adjunction t p f := rfl

theorem adjunctionEquiv_coordinateForm (t : ℂ) (i : Fin 4) (e : Fin 2) (p : Fiber t)
    (hp : p ∈ FixedFiber.source t i e) :
    adjunctionEquiv t p (tangentCoordinateForm i e (FixedFiber.inclusion t p)) =
      FixedFiber.tangentCoordinateForm t i e p := adjunction_coordinateForm t i e p hp

theorem adjunctionEquiv_symm_coordinateForm (t : ℂ) (i : Fin 4) (e : Fin 2) (p : Fiber t)
    (hp : p ∈ FixedFiber.source t i e) :
    (adjunctionEquiv t p).symm (FixedFiber.tangentCoordinateForm t i e p) =
      tangentCoordinateForm i e (FixedFiber.inclusion t p) := by
  apply (adjunctionEquiv t p).injective
  rw [LinearEquiv.apply_symm_apply,adjunctionEquiv_coordinateForm t i e p hp]

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalCanonical
