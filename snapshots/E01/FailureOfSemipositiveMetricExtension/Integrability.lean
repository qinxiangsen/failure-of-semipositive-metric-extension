import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Tactic

namespace FailureOfSemipositiveMetricExtension
open MeasureTheory Set

/-- The exact normal radial integral criterion, not a sheaf identification. -/
theorem radial_integrability_iff (k m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun r : ℝ => r ^ (2 * (k : ℝ) - (m : ℝ) + 1)) (Ioo 0 ε) ↔
    m / 2 ≤ k := by
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff hε]
  have hdiscrete : m / 2 ≤ k ↔ m < 2 * k + 2 := by omega
  rw [hdiscrete]
  constructor
  · intro h
    have h' : (m : ℝ) < ((2 * k + 2 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast h'
  · intro h
    have h' : (m : ℝ) < ((2 * k + 2 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'; linarith

theorem threshold_equivalence (k m : ℕ) :
    (m : ℝ) / 2 - 1 < (k : ℝ) ↔ m / 2 ≤ k := by
  have hdiscrete : m / 2 ≤ k ↔ m < 2 * k + 2 := by omega
  rw [hdiscrete]
  constructor
  · intro h
    have h' : (m : ℝ) < ((2 * k + 2 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast h'
  · intro h
    have h' : (m : ℝ) < ((2 * k + 2 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'; linarith

theorem fourth_power_threshold (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun r : ℝ => r ^ (2 * (k : ℝ) - 4 + 1)) (Ioo 0 ε) ↔ 2 ≤ k := by
  simpa using radial_integrability_iff k 4 ε hε

theorem weight_comparison (ψ φ C : ℝ) (h : φ - C ≤ ψ) :
    Real.exp (-4 * ψ) ≤ Real.exp (4 * C) * Real.exp (-4 * φ) := by
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

/-- General tensor power version of the pointwise weight bound. -/
theorem tensor_weight_comparison (ψ φ C m : ℝ) (hm : 0 ≤ m) (h : φ - C ≤ ψ) :
    Real.exp (-m * ψ) ≤ Real.exp (m * C) * Real.exp (-m * φ) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left h hm]

/-- The measure-theoretic domination step for finite real local weights.
The measurable target hypothesis is explicit, and the conclusion is actual
Lebesgue integrability. Extended-valued metric weights still require a bridge. -/
theorem integrable_weighted_of_comparison {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (a φ ψ : α → ℝ) (m C : ℝ) (hm : 0 ≤ m)
    (ha : ∀ x, 0 ≤ a x) (hcmp : ∀ x, φ x - C ≤ ψ x)
    (hsource : Integrable (fun x => a x * Real.exp (-m * φ x)) μ)
    (htarget : AEStronglyMeasurable (fun x => a x * Real.exp (-m * ψ x)) μ) :
    Integrable (fun x => a x * Real.exp (-m * ψ x)) μ := by
  apply (hsource.const_mul (Real.exp (m*C))).mono' htarget
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (ha x) (Real.exp_pos _).le)]
  calc
    a x * Real.exp (-m * ψ x) ≤ a x * (Real.exp (m*C) * Real.exp (-m * φ x)) :=
      mul_le_mul_of_nonneg_left (tensor_weight_comparison (ψ x) (φ x) C m hm (hcmp x)) (ha x)
    _ = Real.exp (m*C) * (a x * Real.exp (-m * φ x)) := by ring
end FailureOfSemipositiveMetricExtension
