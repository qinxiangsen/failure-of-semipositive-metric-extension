import FailureOfSemipositiveMetricExtension.GlobalLineBundle
import FailureOfSemipositiveMetricExtension.GlobalAnalyticMaps

/-! Actual analytic structure of the global ambient-multidegree line bundles. -/
namespace FailureOfSemipositiveMetricExtension.GlobalLineBundle
noncomputable section
open Set Bundle IsManifold FailureOfSemipositiveMetricExtension.GlobalIncidence
open scoped Manifold ContDiff

theorem gain_contMDiffOn (a : ℤ) (b : Fin 4 → ℤ) (i j : Index) (n : WithTop ℕ∞) :
    ContMDiffOn 𝓘(ℂ,ChartCoord) 𝓘(ℂ) n (gain a b i j) (baseSet i ∩ baseSet j) := by
  apply ContMDiffOn.smul
  · exact (FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle.gain_contMDiffOn a i.1 j.1 n).comp
      (blowdown_contMDiff n).contMDiffOn (fun _ hp => ⟨hp.1.1,hp.2.1⟩)
  · have h (r : Fin 4) := (FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.gain_contMDiffOn (b r) (i.2 r) (j.2 r) n).comp
      (direction_contMDiff r n).contMDiffOn (s := baseSet i ∩ baseSet j)
        (fun _ hp => ⟨hp.1.2 r,hp.2.2 r⟩)
    simpa only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,smul_eq_mul,Function.comp_apply] using
      (h 0).smul ((h 1).smul ((h 2).smul (h 3)))

instance core_isContMDiff (a : ℤ) (b : Fin 4 → ℤ) (n : WithTop ℕ∞) :
    (core a b).IsContMDiff 𝓘(ℂ,ChartCoord) n where
  contMDiffOn_coordChange i j := (gain_contMDiffOn a b i j n).smul contMDiffOn_const

theorem actual_analytic_vectorBundle (a : ℤ) (b : Fin 4 → ℤ) :
    ContMDiffVectorBundle ω ℂ (core a b).Fiber 𝓘(ℂ,ChartCoord) := inferInstance
end
end FailureOfSemipositiveMetricExtension.GlobalLineBundle
