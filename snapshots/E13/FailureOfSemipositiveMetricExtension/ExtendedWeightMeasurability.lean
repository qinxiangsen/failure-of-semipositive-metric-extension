import FailureOfSemipositiveMetricExtension.ExtendedWeightComparison
import FailureOfSemipositiveMetricExtension.Plurisubharmonic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! Genuine measurability of singular metric densities, derived from upper
semicontinuity of the extended weight, including minus-infinity values. -/
namespace FailureOfSemipositiveMetricExtension.Multiplier
noncomputable section
open Set MeasureTheory Topology
open scoped ENNReal

theorem exponentialWeight_pos (u : WithBot ℝ) : 0 < exponentialWeight u := by
  cases u with
  | bot => simp
  | coe u => rw [exponentialWeight_coe]; exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)

theorem lt_exponentialWeight_iff (c : ℝ≥0∞) (hc : c ≠ ⊤) (hc0 : c ≠ 0)
    (u : WithBot ℝ) :
    c < exponentialWeight u ↔ u < ((-Real.log c.toReal : ℝ) : WithBot ℝ) := by
  cases u with
  | bot => simp [hc.lt_top]
  | coe u =>
    rw [exponentialWeight_coe,ENNReal.lt_ofReal_iff_toReal_lt hc,
      ← Real.log_lt_iff_lt_exp (ENNReal.toReal_pos hc0 hc),WithBot.coe_lt_coe]
    constructor <;> intro h <;> linarith

/-- Upper-semicontinuous weights have lower-semicontinuous positive extended
exponentials. No topology on WithBot R is silently assumed. -/
theorem exponentialWeight_lowerSemicontinuous {M : Type*} [TopologicalSpace M]
    {u : M → WithBot ℝ} (hu : UpperSemicontinuous u) :
    LowerSemicontinuous (fun p => exponentialWeight (u p)) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro c
  change IsOpen {p | c < exponentialWeight (u p)}
  by_cases hc : c = ⊤
  · subst c
    simp
  by_cases hc0 : c = 0
  · subst c
    simp [exponentialWeight_pos]
  have he : {p | c < exponentialWeight (u p)} =
      {p | u p < ((-Real.log c.toReal : ℝ) : WithBot ℝ)} := by
    ext p
    exact lt_exponentialWeight_iff c hc hc0 (u p)
  rw [he]
  exact hu.isOpen_preimage _

theorem exponentialWeight_measurable {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [OpensMeasurableSpace M]
    {u : M → WithBot ℝ} (hu : UpperSemicontinuous u) :
    Measurable (fun p => exponentialWeight (u p)) :=
  (exponentialWeight_lowerSemicontinuous hu).measurable

/-- Restricting an upper-semicontinuous-on-set weight gives an actual globally
upper-semicontinuous function on that subtype. -/
theorem upperSemicontinuous_restrict {M : Type*} [TopologicalSpace M]
    {u : M → WithBot ℝ} {U : Set M} (hu : UpperSemicontinuousOn u U) :
    UpperSemicontinuous (fun p : U => u p) := by
  intro p c hc
  have h := hu p p.property c hc
  rw [nhdsWithin_eq_map_subtype_coe p.property] at h
  exact h

theorem exponentialWeight_restrict_measurable {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [OpensMeasurableSpace M]
    {u : M → WithBot ℝ} {U : Set M} (hu : UpperSemicontinuousOn u U) :
    Measurable (fun p : U => exponentialWeight (u p)) :=
  exponentialWeight_measurable (upperSemicontinuous_restrict hu)

end
end FailureOfSemipositiveMetricExtension.Multiplier
