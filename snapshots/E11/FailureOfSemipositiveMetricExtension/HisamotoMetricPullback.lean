import FailureOfSemipositiveMetricExtension.HisamotoBundleIsomorphism
import FailureOfSemipositiveMetricExtension.PlurisubharmonicRestriction

/-! Every compatible semipositive singular metric on an actual ruling fibre
extends to the actual ruling neighbourhood by pullback. The transition functions
here are those of the incidence bundle, not an assumed product line bundle. -/
namespace FailureOfSemipositiveMetricExtension.Hisamoto.LineBundle
noncomputable section
open Set

/-- A metric on the actual restriction to the ruling fibre, expressed in the
two frames obtained by restricting the ambient incidence bundle atlas. -/
structure FibreMetric (a b : ℤ) (i : Fin 2) (t : ℂ) where
  weight : Fin 2 → Direction → WithBot ℝ
  compatible : ∀ j k p, p ∈ ProjectiveLine.chartSet j ∩ ProjectiveLine.chartSet k →
    weight k p = weight j p +
      (Real.log (Complex.normSq (gain a b (i,j) (i,k) (localParam i (p,t)))) : ℝ)

def FibreMetric.Semipositive {a b : ℤ} {i : Fin 2} {t : ℂ} (h : FibreMetric a b i t) : Prop :=
  ∀ j k, PlurisubharmonicOn (fun s => h.weight j (ProjectiveLine.param k s)) (ProjectiveLine.overlap k j)

/-- Metric on the actual open ruling neighbourhood. The two indicated
ambient line-bundle frames cover that whole neighbourhood. -/
structure NeighbourhoodMetric (a b : ℤ) (i : Fin 2) where
  weight : Fin 2 → Point → WithBot ℝ
  compatible : ∀ j k q, q ∈ baseSet (i,j) ∩ baseSet (i,k) →
    weight k q = weight j q + (Real.log (Complex.normSq (gain a b (i,j) (i,k) q)) : ℝ)

/-- This is exactly the domain of a valid bundle frame in a surface affine chart. -/
def metricChartDomain (i j k : Fin 2) : Set Coord :=
  affineParam i k ⁻¹' baseSet (i,j)

theorem metricChartDomain_eq (i j k : Fin 2) :
    metricChartDomain i j k = ProjectiveLine.overlap k j ×ˢ (univ : Set ℂ) := by
  ext q
  change affineParam i k q ∈ (affineChart i j).source ↔ _
  rw [affineParam,localParam_mem_affineChart_iff,ProjectiveLine.param_mem_chartSet_iff]
  simp

def NeighbourhoodMetric.Semipositive {a b : ℤ} {i : Fin 2} (h : NeighbourhoodMetric a b i) : Prop :=
  ∀ j k, PlurisubharmonicOn (fun q => h.weight j (affineParam i k q)) (metricChartDomain i j k)

/-- The extension is literal pullback by the analytically certified first
coordinate of the ruling-product chart. -/
def FibreMetric.extend {a b : ℤ} {i : Fin 2} {t : ℂ} (h : FibreMetric a b i t) :
    NeighbourhoodMetric a b i where
  weight j q := h.weight j (fiberDirection i (blowdown q))
  compatible j k q hq := by
    have hj := (mem_affineChart_source i j q).mp hq.1
    have hk := (mem_affineChart_source i k q).mp hq.2
    have hh := h.compatible j k (fiberDirection i (blowdown q)) ⟨hj.2,hk.2⟩
    rw [gain_local a b i j k _ hk.2] at hh
    have hg : gain a b (i,j) (i,k) q =
        ProjectiveLineBundle.gain a j k (fiberDirection i (blowdown q)) := by
      conv_lhs => rw [← localParam_localCoordinates i q hj.1]
      exact gain_local a b i j k _ hk.2
    rw [hg]
    exact hh

@[simp] theorem FibreMetric.extend_localParam {a b : ℤ} {i : Fin 2} {t : ℂ}
    (h : FibreMetric a b i t) (j : Fin 2) (p : Direction) (u : ℂ) :
    h.extend.weight j (localParam i (p,u)) = h.weight j p := by
  simp [FibreMetric.extend]

theorem FibreMetric.extend_semipositive {a b : ℤ} {i : Fin 2} {t : ℂ}
    (h : FibreMetric a b i t) (hh : h.Semipositive) : h.extend.Semipositive := by
  intro j k
  rw [metricChartDomain_eq]
  have hm : MapsTo (ContinuousLinearMap.fst ℂ ℂ ℂ)
      (ProjectiveLine.overlap k j ×ˢ (univ : Set ℂ)) (ProjectiveLine.overlap k j) :=
    fun q hq => hq.1
  have hp := (hh j k).comp_complexLinear (ProjectiveLine.overlap_isOpen k j)
    (ContinuousLinearMap.fst ℂ ℂ ℂ) hm
  simpa only [affineParam,FibreMetric.extend_localParam] using hp

/-- All original weights are recovered exactly on the prescribed fibre. -/
theorem every_semipositive_metric_extends (a b : ℤ) (i : Fin 2) (t : ℂ)
    (h : FibreMetric a b i t) (hh : h.Semipositive) :
    ∃ H : NeighbourhoodMetric a b i, H.Semipositive ∧
      ∀ j p, H.weight j (localParam i (p,t)) = h.weight j p :=
  ⟨h.extend,h.extend_semipositive hh,fun j p => h.extend_localParam j p t⟩

/-- Hisamoto Example 4.12's degree-two line bundle has no local obstruction
along any ruling fibre: every semipositive singular metric extends. -/
theorem hisamoto_every_semipositive_metric_extends (i : Fin 2) (t : ℂ)
    (h : FibreMetric 2 (-1) i t) (hh : h.Semipositive) :
    ∃ H : NeighbourhoodMetric 2 (-1) i, H.Semipositive ∧
      ∀ j p, H.weight j (localParam i (p,t)) = h.weight j p :=
  every_semipositive_metric_extends 2 (-1) i t h hh

end
end FailureOfSemipositiveMetricExtension.Hisamoto.LineBundle
