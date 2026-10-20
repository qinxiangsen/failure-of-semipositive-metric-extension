import FailureOfSemipositiveMetricExtension.ComplexThreefoldJacobian
import FailureOfSemipositiveMetricExtension.FixedFiberCanonicalForms

/-! Ordered coordinate adjunction: contracting dz₁∧dz₂∧dt against a vector
with dt=1 gives dz₁∧dz₂ on vertical vectors, with the correct positive sign. -/
namespace FailureOfSemipositiveMetricExtension.ComplexThreefoldJacobian
noncomputable section

theorem coordinateVolume_formula (v : Fin 3 → Coord) :
    coordinateVolume v =
      (v 0).1.1 * (v 1).1.2 * (v 2).2 +
      (v 1).1.1 * (v 2).1.2 * (v 0).2 +
      (v 2).1.1 * (v 0).1.2 * (v 1).2 -
      (v 2).1.1 * (v 1).1.2 * (v 0).2 -
      (v 1).1.1 * (v 0).1.2 * (v 2).2 -
      (v 0).1.1 * (v 2).1.2 * (v 1).2 := by
  rw [coordinateVolume,Basis.det_apply,Matrix.det_fin_three]
  have h0 : finSumFinEquiv.symm (0 : Fin 3) = (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 1) := rfl
  have h1 : finSumFinEquiv.symm (1 : Fin 3) = (Sum.inl (1 : Fin 2) : Fin 2 ⊕ Fin 1) := rfl
  have h2 : finSumFinEquiv.symm (2 : Fin 3) = (Sum.inr (0 : Fin 1) : Fin 2 ⊕ Fin 1) := rfl
  simp [Basis.toMatrix_apply,coordinateBasis,Basis.coe_finTwoProd_repr,h0,h1,h2]
  <;> ring

theorem coordinateVolume_normal_vertical (n : Coord) (hn : n.2 = 1)
    (v : Fin 2 → ComplexSurfaceJacobian.Coord) :
    coordinateVolume (Matrix.vecCons n (fun i => (v i,0))) = ComplexSurfaceJacobian.coordinateVolume v := by
  rw [coordinateVolume_formula,ComplexSurfaceJacobian.coordinateVolume,Basis.det_apply,Matrix.det_fin_two]
  simp [Basis.toMatrix_apply,Basis.coe_finTwoProd_repr,hn]

/-- Intrinsic contraction is independent of the horizontal part of the chosen
normal vector, provided the parameter differential evaluates to one. -/
theorem coordinateVolume_contraction (n : Coord) (hn : n.2 = 1) :
    (coordinateVolume.curryLeft n).compLinearMap
      (LinearMap.inl ℂ (ℂ × ℂ) ℂ) = ComplexSurfaceJacobian.coordinateVolume := by
  ext v
  exact coordinateVolume_normal_vertical n hn v

end
end FailureOfSemipositiveMetricExtension.ComplexThreefoldJacobian
