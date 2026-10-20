import FailureOfSemipositiveMetricExtension.SingularHermitianWeights
import FailureOfSemipositiveMetricExtension.Semicontinuity

/-! Actual global relative potentials of compatible extended metric weights.
The compact upper-bound step is proved without replacing the bundle by an
abstract numerical model, and without any curvature or Siu assumption. -/
namespace FailureOfSemipositiveMetricExtension
noncomputable section
open Set Filter
open scoped Topology

theorem upperSemicontinuousOn_withBot_add_real {X : Type*} [TopologicalSpace X]
    (u : X → WithBot ℝ) (v : X → ℝ) (U : Set X)
    (hu : UpperSemicontinuousOn u U) (hv : ContinuousOn v U) :
    UpperSemicontinuousOn (fun x => u x + (v x : WithBot ℝ)) U := by
  intro p hp c hc
  cases c with
  | bot => exact (not_lt_bot hc).elim
  | coe c =>
    have hex : ∃ A B : ℝ, u p < (A : WithBot ℝ) ∧ v p < B ∧ A+B ≤ c := by
      cases he : u p with
      | bot => exact ⟨c-v p-1,v p+1,by simp [he],by linarith,by linarith⟩
      | coe a =>
        have hh : a+v p < c := by simpa only [he,← WithBot.coe_add,WithBot.coe_lt_coe] using hc
        exact ⟨(c+a-v p)/2,(c-a+v p)/2,by simpa [he] using (show a<(c+a-v p)/2 by linarith),by linarith,by linarith⟩
    obtain ⟨A,B,hA,hB,hAB⟩ := hex
    filter_upwards [hu p hp A hA,(hv p hp).eventually (isOpen_Iio.mem_nhds hB)] with q hqA hqB
    cases he : u q with
    | bot => simp [he]
    | coe a =>
      have ha : a < A := by simpa [he] using hqA
      simpa only [he,← WithBot.coe_add,WithBot.coe_lt_coe] using (show a+v q < c by linarith)

end
end FailureOfSemipositiveMetricExtension

namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Filter IsManifold
open scoped Manifold ContDiff Topology

/-- The difference from a smooth metric, glued using the actual transition law. -/
def relativePotential {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ}
    (h : SingularHermitianWeight t a b) (hRef : SmoothHermitianMetric t a b)
    (p : Fiber t) : WithBot ℝ :=
  let i := (core t a b).indexAt p
  h.weight i p + (Real.log (hRef.coefficient i p) : ℝ)

theorem relativePotential_eq_frame {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ}
    (h : SingularHermitianWeight t a b) (hRef : SmoothHermitianMetric t a b)
    (i : Index) (p : Fiber t) (hp : p ∈ baseSet t i) :
    relativePotential h hRef p = h.weight i p + (Real.log (hRef.coefficient i p) : ℝ) := by
  let j := (core t a b).indexAt p
  have hj : p ∈ baseSet t j := (core t a b).mem_baseSet_at p
  have ht := h.compatible i j p ⟨hp,hj⟩
  have hr := congrArg Real.log (hRef.compatible i j p ⟨hp,hj⟩)
  rw [Real.log_mul (ne_of_gt (hRef.positive j p hj))
    (ne_of_gt (Complex.normSq_pos.mpr (gain_ne_zero t a b i j p ⟨hp,hj⟩)))] at hr
  change h.weight j p + _ = _
  rw [ht,add_assoc,← WithBot.coe_add]
  congr 1
  exact congrArg (fun x : ℝ => (x : WithBot ℝ)) (by linarith :
    Real.log (Complex.normSq (gain t a b i j p)) + Real.log (hRef.coefficient j p) =
      Real.log (hRef.coefficient i p))

theorem relativePotential_upperSemicontinuous {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ}
    (h : SingularHermitianWeight t a b) (hRef : SmoothHermitianMetric t a b)
    (hu : ∀ i, UpperSemicontinuousOn (h.weight i) (baseSet t i)) :
    UpperSemicontinuous (relativePotential h hRef) := by
  intro p c hc
  let i := (core t a b).indexAt p
  have hp : p ∈ baseSet t i := (core t a b).mem_baseSet_at p
  have hlog : ContinuousOn (fun q => Real.log (hRef.coefficient i q)) (baseSet t i) := by
    exact Real.continuousOn_log.comp (hRef.smooth i).continuousOn
      (fun q hq => ne_of_gt (hRef.positive i q hq))
  have hlocal := FailureOfSemipositiveMetricExtension.upperSemicontinuousOn_withBot_add_real
    (h.weight i) (fun q => Real.log (hRef.coefficient i q)) (baseSet t i) (hu i) hlog
  rw [relativePotential_eq_frame h hRef i p hp] at hc
  have hev := hlocal p hp c hc
  rw [nhdsWithin_eq_nhds.mpr ((baseSet_isOpen t i).mem_nhds hp)] at hev
  filter_upwards [hev,(baseSet_isOpen t i).mem_nhds hp] with q hq hqU
  rwa [relativePotential_eq_frame h hRef i q hqU]

/-- Any upper-semicontinuous compatible weight has a single global upper bound
relative to a smooth metric, on the actual compact fibre. -/
theorem weight_le_smooth_add_const {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ}
    (h : SingularHermitianWeight t a b) (hRef : SmoothHermitianMetric t a b)
    (hu : ∀ i, UpperSemicontinuousOn (h.weight i) (baseSet t i)) :
    ∃ C : ℝ, ∀ i p, p ∈ baseSet t i →
      h.weight i p ≤ (smoothMetricWeight hRef).weight i p + (C : WithBot ℝ) := by
  obtain ⟨C,hC⟩ := FailureOfSemipositiveMetricExtension.usc_withBot_bounded_above (relativePotential h hRef)
    (relativePotential_upperSemicontinuous h hRef hu)
  refine ⟨C,?_⟩
  intro i p hp
  have hh := hC p
  rw [relativePotential_eq_frame h hRef i p hp] at hh
  cases he : h.weight i p with
  | bot => simp [he]
  | coe r =>
    have hr : r + Real.log (hRef.coefficient i p) ≤ C := by simpa only [he,← WithBot.coe_add,WithBot.coe_le_coe] using hh
    simp only [he,smoothMetricWeight,← WithBot.coe_add,WithBot.coe_le_coe]
    linarith

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
