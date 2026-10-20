import FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle
import FailureOfSemipositiveMetricExtension.GlobalChartAnalyticMaps

/-! Analytic projectivization of a nonzero three-vector for the actual affine-atlas
projective plane, with exact normalized coordinate and bundle-ratio formulas. -/
namespace FailureOfSemipositiveMetricExtension.ProjectivePlane
noncomputable section
open Set Topology
open scoped Manifold ContDiff

def vectorPoint (v : Fin 3 → ℂ) : Point :=
  if h : v = 0 then param 0 (0,0) else Projectivization.mk ℂ v h

theorem vectorPoint_eq_mk (v : Fin 3 → ℂ) (hv : v ≠ 0) :
    vectorPoint v = Projectivization.mk ℂ v hv := by simp [vectorPoint,hv]

theorem vectorPoint_eq_param (i : Fin 3) (v : Fin 3 → ℂ) (hi : v i ≠ 0) :
    vectorPoint v = param i (normalize i v) := by
  have hv : v ≠ 0 := fun h => hi (congrFun h i)
  rw [vectorPoint_eq_mk v hv]
  exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨v i,vector_normalize i v hi⟩

theorem normalize_contDiffAt (i : Fin 3) (n : WithTop ℕ∞) (v : Fin 3 → ℂ) (hi : v i ≠ 0) :
    ContDiffAt ℂ n (normalize i) v := by
  change ContDiffAt ℂ n (fun w => normalize i w) v
  fin_cases i <;> dsimp [normalize] <;> fun_prop (disch := assumption)

theorem vectorPoint_contMDiffAt (n : WithTop ℕ∞) (v : Fin 3 → ℂ) (hv : v ≠ 0) :
    ContMDiffAt 𝓘(ℂ,Fin 3 → ℂ) 𝓘(ℂ,ℂ × ℂ) n vectorPoint v := by
  have hex : ∃ i, v i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (funext h)
  obtain ⟨i,hi⟩ := hex
  have h := (param_contMDiff i n).contMDiffAt.comp v (normalize_contDiffAt i n v hi).contMDiffAt
  apply h.congr_of_eventuallyEq
  filter_upwards [(continuous_apply i).continuousAt.eventually_ne hi] with w hw
  exact vectorPoint_eq_param i w hw

theorem vectorPoint_mem_chartSet_iff (i : Fin 3) (v : Fin 3 → ℂ) (hv : v ≠ 0) :
    vectorPoint v ∈ chartSet i ↔ v i ≠ 0 := by
  constructor
  · rintro ⟨q,hq⟩ hi
    rw [vectorPoint_eq_mk v hv] at hq
    obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp hq
    have h := congrFun ha i
    exact zero_ne_one (by simpa only [Pi.smul_apply,smul_eq_mul,vector_self,hi,mul_zero] using h)
  · intro hi
    rw [vectorPoint_eq_param i v hi]
    exact param_mem_chartSet i _

end
end FailureOfSemipositiveMetricExtension.ProjectivePlane
