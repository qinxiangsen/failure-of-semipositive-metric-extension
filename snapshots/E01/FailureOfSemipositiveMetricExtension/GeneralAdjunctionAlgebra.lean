import FailureOfSemipositiveMetricExtension.GeneralCaoFiniteNormInterface

/-! Correct normal-last coordinate adjunction in every complex dimension,
including the parity discrepancy with a normal-first convention. -/
namespace FailureOfSemipositiveMetricExtension.GeneralCao
noncomputable section

theorem coordinateVolume_normal_last (n : ℕ) (v : Fin n → Coord n) (ν : Coord (n+1))
    (hν : ν (Fin.last n) = 1) :
    coordinateVolume (n+1) (Fin.snoc (fun k => Fin.snoc (v k) 0) ν) = coordinateVolume n v := by
  classical
  have hmat : ((Pi.basisFun ℂ (Fin (n+1))).toMatrix
      (Fin.snoc (fun k => Fin.snoc (v k) 0) ν)).submatrix Fin.castSucc Fin.castSucc =
        (Pi.basisFun ℂ (Fin n)).toMatrix v := by
    ext i j
    simp [Matrix.submatrix_apply,Basis.toMatrix_apply]
  have hsign : (-1 : ℂ)^n * (-1 : ℂ)^n = 1 := by rw [← mul_pow]; simp
  unfold coordinateVolume
  rw [Basis.det_apply,Basis.det_apply]
  rw [Matrix.det_succ_row _ (Fin.last n),Fin.sum_univ_castSucc]
  simp [Basis.toMatrix_apply,Pi.basisFun_repr,Fin.snoc_last,Fin.snoc_castSucc,hν,Fin.succAbove_last,pow_add,hmat,hsign]


theorem alternating_normal_last_first {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (n : ℕ) (F : V [⋀^Fin (n+1)]→ₗ[ℂ] ℂ) (v : Fin n → V) (ν : V) :
    F (Fin.snoc v ν) = (-1 : ℂ)^n * F (Fin.cons ν v) := by
  classical
  rw [Fin.snoc_eq_cons_rotate]
  change F ((Fin.cons ν v) ∘ finRotate (n+1)) = _
  rw [F.map_perm,sign_finRotate]
  simp [Units.smul_def,zsmul_eq_mul]

theorem coordinateVolume_normal_first (n : ℕ) (v : Fin n → Coord n) (ν : Coord (n+1))
    (hν : ν (Fin.last n) = 1) :
    coordinateVolume (n+1) (Fin.cons ν (fun k => Fin.snoc (v k) 0)) =
      (-1 : ℂ)^n * coordinateVolume n v := by
  have he := alternating_normal_last_first n (coordinateVolume (n+1))
    (fun k => Fin.snoc (v k) 0) ν
  rw [coordinateVolume_normal_last n v ν hν] at he
  have hsign : (-1 : ℂ)^n * (-1 : ℂ)^n = 1 := by rw [← mul_pow]; simp
  rw [he,← mul_assoc,hsign,one_mul]

end
end FailureOfSemipositiveMetricExtension.GeneralCao
