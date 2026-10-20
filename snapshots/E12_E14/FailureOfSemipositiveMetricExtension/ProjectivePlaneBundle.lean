import FailureOfSemipositiveMetricExtension.ProjectivePlaneFamily
import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-! Actual complex line bundles on the constructed projective plane, with the
standard homogeneous-degree transition cocycles, for every integer degree.
An algebraic invertible-sheaf equivalence is not asserted here. -/
namespace FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle
noncomputable section
open FailureOfSemipositiveMetricExtension.ProjectivePlane Set Bundle
open scoped Manifold ContDiff

/-- Ratio of homogeneous normalizations, extended off the relevant chart. -/
def ratio (i j : Fin 3) (p : Point) : ℂ := vector j (coordinates j p) i

theorem ratio_self (i : Fin 3) (p : Point) : ratio i i p = 1 := vector_self i _

theorem coordinates_mem_overlap (i j : Fin 3) (p : Point)
    (hi : p ∈ chartSet i) (hj : p ∈ chartSet j) :
    coordinates j p ∈ overlap j i := by
  apply (param_mem_chartSet_iff j i _).mp
  rw [param_coordinates j p hj]
  exact hi

theorem ratio_ne_zero (i j : Fin 3) (p : Point)
    (hi : p ∈ chartSet i) (hj : p ∈ chartSet j) : ratio i j p ≠ 0 :=
  coordinates_mem_overlap i j p hi hj

/-- The triple-overlap cocycle is an exact identity of normalized homogeneous coordinates. -/
theorem ratio_comp (i j l : Fin 3) (p : Point)
    (hj : p ∈ chartSet j) (hl : p ∈ chartSet l) :
    ratio j l p * ratio i j p = ratio i l p := by
  have ht := vector_transition l j (coordinates l p) (coordinates_mem_overlap j l p hj hl)
  have hc : transition l j (coordinates l p) = coordinates j p := by
    rw [← coordinates_transition l j (coordinates l p)
      (coordinates_mem_overlap j l p hj hl),param_coordinates l p hl]
  rw [hc] at ht
  exact congrFun ht i

def gain (d : ℤ) (i j : Fin 3) (p : Point) : ℂ := ratio i j p ^ d

theorem gain_comp (d : ℤ) (i j l : Fin 3) (p : Point)
    (hp : p ∈ chartSet i ∩ chartSet j ∩ chartSet l) :
    gain d j l p * gain d i j p = gain d i l p := by
  dsimp [gain]
  rw [← mul_zpow,ratio_comp i j l p hp.1.2 hp.2]

theorem ratio_continuousOn (i j : Fin 3) : ContinuousOn (ratio i j) (chartSet j) :=
  (vector_component_continuous j i).comp_continuousOn (homeomorphChart j).continuousOn

theorem gain_continuousOn (d : ℤ) (i j : Fin 3) :
    ContinuousOn (gain d i j) (chartSet i ∩ chartSet j) :=
  ((ratio_continuousOn i j).mono inter_subset_right).zpow₀ d
    (fun p hp => Or.inl (ratio_ne_zero i j p hp.1 hp.2))

/-- The true topological complex line bundle of homogeneous degree d. -/
def core (d : ℤ) : VectorBundleCore ℂ Point ℂ (Fin 3) where
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

theorem coordinates_contMDiffOn (j : Fin 3) (n : WithTop ℕ∞) :
    ContMDiffOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) n (coordinates j) (chartSet j) := by
  change ContMDiffOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) n (homeomorphChart j) (homeomorphChart j).source
  apply contMDiffOn_of_mem_maximalAtlas
  apply IsManifold.subset_maximalAtlas
  exact (mem_atlas_iff _).mpr ⟨j,rfl⟩

theorem coordinate_zpow_contDiffOn (d : ℤ) (i j : Fin 3) (n : WithTop ℕ∞) :
    ContDiffOn ℂ n (fun q => vector j q i ^ d) (overlap j i) := by
  have hc : ContDiff ℂ n (fun q : ℂ × ℂ => vector j q i) := by
    fin_cases i <;> fin_cases j <;> dsimp [vector] <;> fun_prop
  cases d with
  | ofNat k => simpa using (hc.pow k).contDiffOn
  | negSucc k =>
    simpa only [zpow_negSucc] using ((hc.pow (k+1)).contDiffOn.inv
      (fun q hq => pow_ne_zero _ hq))

theorem gain_contMDiffOn (d : ℤ) (i j : Fin 3) (n : WithTop ℕ∞) :
    ContMDiffOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) n (gain d i j) (chartSet i ∩ chartSet j) := by
  exact (coordinate_zpow_contDiffOn d i j n).contMDiffOn.comp
    ((coordinates_contMDiffOn j n).mono inter_subset_right)
    (fun p hp => coordinates_mem_overlap i j p hp.1 hp.2)

instance core_isContMDiff (d : ℤ) (n : WithTop ℕ∞) :
    (core d).IsContMDiff 𝓘(ℂ, ℂ × ℂ) n where
  contMDiffOn_coordChange i j := (gain_contMDiffOn d i j n).smul contMDiffOn_const

theorem actual_analytic_vectorBundle (d : ℤ) :
    ContMDiffVectorBundle ω ℂ (core d).Fiber 𝓘(ℂ, ℂ × ℂ) := inferInstance

end
end FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle
