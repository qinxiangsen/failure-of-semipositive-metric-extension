import FailureOfSemipositiveMetricExtension.ProjectiveLine
import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-! The actual analytic homogeneous-degree line bundles on the projective line,
for every positive, zero or negative integer degree. -/
namespace FailureOfSemipositiveMetricExtension.ProjectiveLineBundle
noncomputable section
open FailureOfSemipositiveMetricExtension.ProjectiveLine Set Bundle
open scoped Manifold ContDiff
attribute [local instance] Classical.propDecidable

def ratio (i j : Fin 2) (p : Point) : ℂ := if i = j then 1 else coordinates j p

theorem coordinates_product (i j : Fin 2) (hij : i ≠ j) (p : Point)
    (hi : p ∈ chartSet i) (hj : p ∈ chartSet j) :
    coordinates i p * coordinates j p = 1 :=
  cross_ratio_eq_one i j hij _ _ ((param_coordinates i p hi).trans (param_coordinates j p hj).symm)

theorem ratio_self (i : Fin 2) (p : Point) : ratio i i p = 1 := by simp [ratio]

theorem ratio_ne_zero (i j : Fin 2) (p : Point)
    (hi : p ∈ chartSet i) (hj : p ∈ chartSet j) : ratio i j p ≠ 0 := by
  by_cases hij : i = j
  · simp [ratio,hij]
  · have h := coordinates_product i j hij p hi hj
    simp only [ratio,if_neg hij]
    intro hz
    rw [hz,mul_zero] at h
    exact zero_ne_one h

theorem ratio_comp (i j l : Fin 2) (p : Point)
    (hp : p ∈ chartSet i ∩ chartSet j ∩ chartSet l) :
    ratio j l p * ratio i j p = ratio i l p := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> simp [ratio]
  · exact coordinates_product 0 1 (by decide) p hp.1.1 hp.1.2
  · simpa [mul_comm] using coordinates_product 0 1 (by decide) p hp.1.2 hp.1.1

def gain (d : ℤ) (i j : Fin 2) (p : Point) : ℂ := ratio i j p ^ d

theorem gain_comp (d : ℤ) (i j l : Fin 2) (p : Point)
    (hp : p ∈ chartSet i ∩ chartSet j ∩ chartSet l) :
    gain d j l p * gain d i j p = gain d i l p := by
  dsimp [gain]
  rw [← mul_zpow,ratio_comp i j l p hp]

theorem ratio_continuousOn (i j : Fin 2) : ContinuousOn (ratio i j) (chartSet j) := by
  unfold ratio
  split_ifs
  · exact continuousOn_const
  · exact (homeomorphChart j).continuousOn

theorem gain_continuousOn (d : ℤ) (i j : Fin 2) :
    ContinuousOn (gain d i j) (chartSet i ∩ chartSet j) :=
  ((ratio_continuousOn i j).mono inter_subset_right).zpow₀ d
    (fun p hp => Or.inl (ratio_ne_zero i j p hp.1 hp.2))

def core (d : ℤ) : VectorBundleCore ℂ Point ℂ (Fin 2) where
  baseSet := chartSet
  isOpen_baseSet := chartSet_isOpen
  indexAt p := Classical.choose (charts_cover p)
  mem_baseSet_at p := by
    obtain ⟨q,hq⟩ := Classical.choose_spec (charts_cover p)
    exact ⟨q,hq.symm⟩
  coordChange i j p := gain d i j p • ContinuousLinearMap.id ℂ ℂ
  coordChange_self i p _ v := by simp [gain,ratio_self]
  continuousOn_coordChange i j := (gain_continuousOn d i j).smul continuousOn_const
  coordChange_comp i j l p hp v := by
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul]
    rw [← mul_assoc,gain_comp d i j l p hp]

theorem fiber_finrank (d : ℤ) (p : Point) : Module.finrank ℂ ((core d).Fiber p) = 1 :=
  Module.finrank_self ℂ

theorem coordinates_contMDiffOn (j : Fin 2) (n : WithTop ℕ∞) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) n (coordinates j) (chartSet j) := by
  change ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) n (homeomorphChart j) (homeomorphChart j).source
  apply contMDiffOn_of_mem_maximalAtlas
  apply IsManifold.subset_maximalAtlas
  exact (mem_atlas_iff _).mpr ⟨j,rfl⟩

theorem scalar_zpow_contDiffOn (d : ℤ) (n : WithTop ℕ∞) :
    ContDiffOn ℂ n (fun z : ℂ => z ^ d) {z | z ≠ 0} := by
  cases d with
  | ofNat k => simpa using (contDiff_id.pow k).contDiffOn
  | negSucc k =>
    simpa only [zpow_negSucc] using ((contDiff_id.pow (k+1)).contDiffOn.inv
      (fun z hz => pow_ne_zero _ hz))

theorem gain_contMDiffOn (d : ℤ) (i j : Fin 2) (n : WithTop ℕ∞) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) n (gain d i j) (chartSet i ∩ chartSet j) := by
  change ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) n (fun p => (if i = j then 1 else coordinates j p) ^ d) _
  by_cases hij : i = j
  · simp only [if_pos hij,one_zpow]; exact contMDiffOn_const
  · have hm : MapsTo (coordinates j) (chartSet i ∩ chartSet j) {z : ℂ | z ≠ 0} := by
      intro p hp
      simpa only [ratio,if_neg hij] using ratio_ne_zero i j p hp.1 hp.2
    simpa only [if_neg hij,Function.comp_apply] using (scalar_zpow_contDiffOn d n).contMDiffOn.comp
      ((coordinates_contMDiffOn j n).mono inter_subset_right) hm

instance core_isContMDiff (d : ℤ) (n : WithTop ℕ∞) : (core d).IsContMDiff 𝓘(ℂ) n where
  contMDiffOn_coordChange i j := (gain_contMDiffOn d i j n).smul contMDiffOn_const

theorem actual_analytic_vectorBundle (d : ℤ) :
    ContMDiffVectorBundle ω ℂ (core d).Fiber 𝓘(ℂ) := inferInstance
end
end FailureOfSemipositiveMetricExtension.ProjectiveLineBundle
