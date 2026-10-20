import FailureOfSemipositiveMetricExtension.GeneralTensorModelEquiv

/-! A genuine analytic tensor-power line bundle, with its fibre model linked
by a proved linear equivalence to mathlib's actual m-fold tensor product. -/
namespace FailureOfSemipositiveMetricExtension.GeneralCao
noncomputable section
open Set Bundle IsManifold
open scoped Manifold ContDiff TensorProduct

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coord (n+1)) M]
    {J : Type} (L : AnalyticLine n (M := M) J)

namespace AnalyticLine

theorem gain_self (i : J) (p : M) (hp : p ∈ L.core.baseSet i) : L.gain i i p = 1 := by
  simpa only [L.coordChange_eq,mul_one] using L.core.coordChange_self i p hp 1

theorem gain_comp (i j k : J) (p : M) (hp : p ∈ (L.core.baseSet i ∩ L.core.baseSet j) ∩ L.core.baseSet k) :
    L.gain j k p * L.gain i j p = L.gain i k p := by
  simpa only [L.coordChange_eq,mul_one] using L.core.coordChange_comp i j k p hp 1

theorem gain_ne_zero (i j : J) (p : M) (hp : p ∈ L.core.baseSet i ∩ L.core.baseSet j) : L.gain i j p ≠ 0 := by
  have he := L.gain_comp i j i p ⟨hp,hp.1⟩
  rw [L.gain_self i p hp.1] at he
  exact (mul_ne_zero_iff.mp (he ▸ one_ne_zero)).2

theorem gain_analytic (i j : J) :
    ContMDiffOn 𝓘(ℂ,Coord (n+1)) 𝓘(ℂ) ω (L.gain i j) (L.core.baseSet i ∩ L.core.baseSet j) := by
  have he : (fun p => L.core.coordChange i j p (1 : ℂ)) = L.gain i j := by
    funext p; rw [L.coordChange_eq,mul_one]
  rw [← he]
  exact (L.analytic.contMDiffOn_coordChange i j).clm_apply contMDiffOn_const

theorem powerGain_analytic (m : ℕ) (i j : J) :
    ContMDiffOn 𝓘(ℂ,Coord (n+1)) 𝓘(ℂ) ω (fun p => L.gain i j p ^ m)
      (L.core.baseSet i ∩ L.core.baseSet j) := by
  induction m with
  | zero => simpa using (contMDiffOn_const : ContMDiffOn 𝓘(ℂ,Coord (n+1)) 𝓘(ℂ) ω (fun _ : M => (1 : ℂ)) _)
  | succ m ih => simpa only [pow_succ,smul_eq_mul] using ih.smul (L.gain_analytic i j)

def powerCore (m : ℕ) : VectorBundleCore ℂ M ℂ J where
  baseSet := L.core.baseSet
  isOpen_baseSet := L.core.isOpen_baseSet
  indexAt := L.core.indexAt
  mem_baseSet_at := L.core.mem_baseSet_at
  coordChange i j p := L.gain i j p ^ m • ContinuousLinearMap.id ℂ ℂ
  coordChange_self i p hp v := by simp [L.gain_self i p hp]
  continuousOn_coordChange i j := (L.powerGain_analytic m i j).continuousOn.smul continuousOn_const
  coordChange_comp i j k p hp v := by
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul]
    rw [← mul_assoc,← mul_pow,L.gain_comp i j k p hp]

instance powerCore_analytic (m : ℕ) : (L.powerCore m).IsContMDiff 𝓘(ℂ,Coord (n+1)) ω where
  contMDiffOn_coordChange i j := (L.powerGain_analytic m i j).smul contMDiffOn_const

def powerLine (m : ℕ) : AnalyticLine n (M := M) J where
  core := L.powerCore m
  analytic := inferInstance
  gain i j p := L.gain i j p ^ m
  coordChange_eq _ _ _ _ := rfl

def tensorFiberEquiv (m : ℕ) (p : M) :
    TensorPower ℂ m (L.core.Fiber p) ≃ₗ[ℂ] (L.powerCore m).Fiber p := scalarTensorEquiv m

theorem tensorFiberEquiv_frame_change (m : ℕ) (i j : J) (p : M)
    (x : TensorPower ℂ m (L.core.Fiber p)) :
    L.tensorFiberEquiv m p (PiTensorProduct.map
      (fun _ : Fin m => (L.core.coordChange i j p).toLinearMap) x) =
      (L.powerCore m).coordChange i j p (L.tensorFiberEquiv m p x) := by
  have he : (L.core.coordChange i j p).toLinearMap = L.gain i j p • LinearMap.id := by
    apply LinearMap.ext
    intro z
    exact L.coordChange_eq i j p z
  simp only [he]
  exact scalarTensorGain_equiv m (L.gain i j p) x

end AnalyticLine
end
end FailureOfSemipositiveMetricExtension.GeneralCao
