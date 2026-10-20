import FailureOfSemipositiveMetricExtension.BlowupAtlas
import FailureOfSemipositiveMetricExtension.BlowupSections
import Mathlib.Topology.VectorBundle.Basic

/-! An actual rank-one topological complex vector bundle on the incidence blow-up,
glued with the k-th powers of the exceptional-coordinate transition. Identification
with the ideal sheaf of the exceptional divisor and its global projective counterpart
is a separate obligation; it is not assumed here. -/
namespace FailureOfSemipositiveMetricExtension.BlowupLineBundle
noncomputable section
open FailureOfSemipositiveMetricExtension.Blowup Set Bundle
attribute [local instance] Classical.propDecidable

def baseSet : Bool → Set Point
  | false => chartXSet
  | true => chartYSet

def gain (k : ℕ) : Bool → Bool → Point → ℂ
  | false, false, _ => 1
  | true, true, _ => 1
  | false, true, p => (coordinatesY p).2 ^ k
  | true, false, p => (coordinatesX p).2 ^ k

theorem slope_product (p : Point) (hx : p ∈ chartXSet) (hy : p ∈ chartYSet) :
    (coordinatesX p).2 * (coordinatesY p).2 = 1 := by
  have h := (X_eq_Y_iff (coordinatesX p).1 (coordinatesX p).2
    (coordinatesY p).1 (coordinatesY p).2).mp
    ((X_coordinatesX p hx).trans (Y_coordinatesY p hy).symm)
  exact h.2

theorem gain_comp (k : ℕ) (i j l : Bool) (p : Point)
    (hp : p ∈ baseSet i ∩ baseSet j ∩ baseSet l) :
    gain k j l p * gain k i j p = gain k i l p := by
  cases i <;> cases j <;> cases l <;> simp [gain]
  · simpa only [← mul_pow,mul_comm,one_pow] using congrArg (fun z : ℂ => z^k)
      (slope_product p hp.1.1 hp.1.2)
  · simpa only [← mul_pow,mul_comm,one_pow] using congrArg (fun z : ℂ => z^k)
      (slope_product p hp.1.2 hp.1.1)

theorem gain_continuousOn (k : ℕ) (i j : Bool) :
    ContinuousOn (gain k i j) (baseSet i ∩ baseSet j) := by
  cases i <;> cases j
  · exact continuousOn_const
  · exact ((continuous_snd.comp_continuousOn homeomorphChartY.continuousOn).mono
      inter_subset_right).pow k
  · exact ((continuous_snd.comp_continuousOn homeomorphChartX.continuousOn).mono
      inter_subset_right).pow k
  · exact continuousOn_const

/-- All gluing, continuity and cocycle obligations for a genuine vector bundle. -/
def core (k : ℕ) : VectorBundleCore ℂ Point ℂ Bool where
  baseSet := baseSet
  isOpen_baseSet i := by cases i; exact chartXSet_isOpen; exact chartYSet_isOpen
  indexAt p := if p ∈ chartXSet then false else true
  mem_baseSet_at p := by
    split_ifs with hx
    · exact hx
    · have hp : p ∈ chartXSet ∪ chartYSet := by rw [chart_sets_cover]; trivial
      exact hp.resolve_left hx
  coordChange i j p := gain k i j p • ContinuousLinearMap.id ℂ ℂ
  coordChange_self i p _ v := by cases i <;> simp [gain]
  continuousOn_coordChange i j := (gain_continuousOn k i j).smul continuousOn_const
  coordChange_comp i j l p hp v := by
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul]
    rw [← mul_assoc,gain_comp k i j l p hp]

/-- The constructed fibres carry the actual mathlib vector-bundle structure. -/
theorem actual_vectorBundle (k : ℕ) : VectorBundle ℂ ℂ (core k).Fiber := inferInstance

/-- Each fibre is a one-dimensional complex vector space. -/
theorem fiber_finrank (k : ℕ) (p : Point) : Module.finrank ℂ ((core k).Fiber p) = 1 := by
  exact Module.finrank_self ℂ

end
end FailureOfSemipositiveMetricExtension.BlowupLineBundle
