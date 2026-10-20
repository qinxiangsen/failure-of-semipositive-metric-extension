import FailureOfSemipositiveMetricExtension.MultiplierGerms
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Exponential domination for genuine extended singular weights. The inequality
includes minus infinity and positive-infinite metric densities, rather than
silently discarding the singular locus. -/
namespace FailureOfSemipositiveMetricExtension.Multiplier
noncomputable section
open Set MeasureTheory
open scoped ENNReal

theorem exponentialWeight_antitone : Antitone exponentialWeight := by
  intro u v huv
  induction u using WithBot.recBotCoe with
  | bot => simp
  | coe u =>
    induction v using WithBot.recBotCoe with
    | bot => simp at huv
    | coe v =>
      rw [exponentialWeight_coe,exponentialWeight_coe]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      exact neg_le_neg (WithBot.coe_le_coe.mp huv)

theorem exponentialWeight_add (u : WithBot ℝ) (c : ℝ) :
    exponentialWeight (u + (c : WithBot ℝ)) =
      ENNReal.ofReal (Real.exp (-c)) * exponentialWeight u := by
  induction u using WithBot.recBotCoe with
  | bot => simp [ENNReal.ofReal_eq_zero,not_le.mpr (Real.exp_pos _)]
  | coe u =>
    simp only [← WithBot.coe_add,exponentialWeight_coe]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
    congr 2
    ring

theorem exponentialWeight_le_of_comparison (u v : WithBot ℝ) (C : ℝ)
    (h : v + ((-C : ℝ) : WithBot ℝ) ≤ u) :
    exponentialWeight u ≤ ENNReal.ofReal (Real.exp C) * exponentialWeight v := by
  have hle := exponentialWeight_antitone h
  simpa only [exponentialWeight_add,neg_neg] using hle

theorem weightedDensity_le_of_comparison (f : ℂ) (m : ℕ) (u v : WithBot ℝ) (C : ℝ)
    (h : v + ((-C : ℝ) : WithBot ℝ) ≤ u) :
    ENNReal.ofReal (Complex.normSq f) * exponentialWeight u ^ m ≤
      ENNReal.ofReal (Real.exp C) ^ m *
        (ENNReal.ofReal (Complex.normSq f) * exponentialWeight v ^ m) := by
  have hh := pow_le_pow_left' (exponentialWeight_le_of_comparison u v C h) m
  have := mul_le_mul_left' hh (ENNReal.ofReal (Complex.normSq f))
  simpa only [mul_pow,mul_left_comm] using this

end
end FailureOfSemipositiveMetricExtension.Multiplier
