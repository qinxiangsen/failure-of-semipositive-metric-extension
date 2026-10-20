import FailureOfSemipositiveMetricExtension.Integrability
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
The local normal-coordinate analytic step for the paper: genuine area integrability on ℂ,
with the polar Jacobian, the integer threshold, and continuous positive factors.
The value assigned by real power at the single point 0 is immaterial because that point
has Lebesgue area zero. No multiplier-ideal sheaf identity is claimed here.
-/

open MeasureTheory Set
open scoped ENNReal

namespace FailureOfSemipositiveMetricExtension

/-- Polar-coordinate reduction of the nonnegative integral of a power on a complex disc. -/
theorem complex_disc_rpow_lintegral (a ε : ℝ) :
    (∫⁻ z : ℂ in Metric.ball 0 ε, ENNReal.ofReal (‖z‖ ^ a)) =
      (∫⁻ r : ℝ in Ioo 0 ε, ENNReal.ofReal (r ^ (a + 1))) *
        ENNReal.ofReal (2 * Real.pi) := by
  let A : Set (ℝ × ℝ) := Iio ε ×ˢ univ
  have hA : MeasurableSet A := measurableSet_Iio.prod MeasurableSet.univ
  calc
    _ = ∫⁻ z : ℂ, (Metric.ball 0 ε).indicator
          (fun z => ENNReal.ofReal (‖z‖ ^ a)) z :=
      (lintegral_indicator measurableSet_ball _).symm
    _ = ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 •
          ((Metric.ball 0 ε).indicator (fun z : ℂ => ENNReal.ofReal (‖z‖ ^ a)))
            (Complex.polarCoord.symm p) :=
      (Complex.lintegral_comp_polarCoord_symm _).symm
    _ = ∫⁻ p in polarCoord.target,
          A.indicator (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 ^ (a + 1))) p := by
      apply setLIntegral_congr_fun polarCoord.open_target.measurableSet
      filter_upwards [] with p hp
      have hp0 : 0 < p.1 := hp.1
      by_cases hpe : p.1 < ε
      · simp only [Set.indicator_of_mem (show Complex.polarCoord.symm p ∈ Metric.ball 0 ε by
            simpa only [Metric.mem_ball, dist_zero_right, Complex.norm_polarCoord_symm,
              abs_of_pos hp0] using hpe),
          Set.indicator_of_mem (show p ∈ A from ⟨hpe, mem_univ _⟩),
          Complex.norm_polarCoord_symm, abs_of_pos hp0, smul_eq_mul]
        rw [← ENNReal.ofReal_mul hp0.le, Real.rpow_add hp0, Real.rpow_one]
        congr 1
        ring
      · simp [Set.indicator, A, Metric.mem_ball, dist_zero_right,
          Complex.norm_polarCoord_symm, abs_of_pos hp0, hpe]
    _ = ∫⁻ p in Ioo 0 ε ×ˢ Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal (p.1 ^ (a + 1)) := by
      rw [setLIntegral_indicator hA]
      have hset : A ∩ polarCoord.target = Ioo 0 ε ×ˢ Ioo (-Real.pi) Real.pi := by
        ext p
        simp only [A, polarCoord_target, mem_inter_iff, mem_prod, mem_Iio, mem_univ,
          and_true, mem_Ioi, mem_Ioo]
        tauto
      rw [hset]
    _ = _ := by
      rw [Measure.volume_eq_prod, setLIntegral_prod]
      · simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
        rw [lintegral_mul_const']
        · congr 1
          congr 1
          ring
        · exact ENNReal.ofReal_ne_top
      · fun_prop

/-- Actual two-dimensional Lebesgue integrability is equivalent to the radial criterion. -/
theorem complex_disc_rpow_integrable_iff_radial (a ε : ℝ) :
    IntegrableOn (fun z : ℂ => ‖z‖ ^ a) (Metric.ball 0 ε) ↔
      IntegrableOn (fun r : ℝ => r ^ (a + 1)) (Ioo 0 ε) := by
  have hmC : AEStronglyMeasurable (fun z : ℂ => ‖z‖ ^ a)
      (volume.restrict (Metric.ball 0 ε)) :=
    (continuous_norm.measurable.pow_const a).aestronglyMeasurable
  have hmR : AEStronglyMeasurable (fun r : ℝ => r ^ (a + 1))
      (volume.restrict (Ioo 0 ε)) :=
    (measurable_id.pow_const (a + 1)).aestronglyMeasurable
  have hposC : 0 ≤ᵐ[volume.restrict (Metric.ball (0 : ℂ) ε)]
      (fun z : ℂ => ‖z‖ ^ a) :=
    Filter.Eventually.of_forall fun z => Real.rpow_nonneg (norm_nonneg z) a
  have hposR : 0 ≤ᵐ[volume.restrict (Ioo 0 ε)] (fun r : ℝ => r ^ (a + 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact Real.rpow_nonneg hr.1.le (a + 1)
  simp only [IntegrableOn, Integrable, hmC, hmR, true_and,
    hasFiniteIntegral_iff_ofReal hposC, hasFiniteIntegral_iff_ofReal hposR]
  rw [complex_disc_rpow_lintegral]
  have hpi : ENNReal.ofReal (2 * Real.pi) ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  exact ⟨fun h => ENNReal.lt_top_of_mul_ne_top_left h.ne hpi,
    fun h => ENNReal.mul_lt_top h ENNReal.ofReal_lt_top⟩

/-- The local power weight occurring in the paper is integrable on a complex disc exactly
at the asserted integer threshold. This is a local analytic statement, not a sheaf identity. -/
theorem complex_disc_integrability_iff (k m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun z : ℂ => ‖z‖ ^ (2 * (k : ℝ) - (m : ℝ))) (Metric.ball 0 ε) ↔
      m / 2 ≤ k := by
  rw [complex_disc_rpow_integrable_iff_radial]
  exact radial_integrability_iff k m ε hε

/-- Removing the origin does not change integrability, since a point has area zero. -/
theorem complex_punctured_disc_integrability_iff (k m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun z : ℂ => ‖z‖ ^ (2 * (k : ℝ) - (m : ℝ)))
      (Metric.ball 0 ε \ {0}) ↔ m / 2 ≤ k := by
  have hnull : (volume : Measure ℂ) ({0} : Set ℂ) = 0 := measure_singleton 0
  have hset : (Metric.ball (0 : ℂ) ε \ ({0} : Set ℂ)) =ᵐ[(volume : Measure ℂ)]
      Metric.ball (0 : ℂ) ε := diff_null_ae_eq_self hnull
  unfold IntegrableOn
  rw [Measure.restrict_congr_set hset]
  exact complex_disc_integrability_iff k m ε hε

/-- A measurable positive factor bounded above and bounded away from zero preserves
integrability of the normal power weight. The bounds are required only on the disc. -/
theorem complex_disc_rpow_mul_integrable_iff (a ε : ℝ) (ψ : ℂ → ℝ) (c C : ℝ)
    (hc : 0 < c) (hψ : AEStronglyMeasurable ψ (volume.restrict (Metric.ball 0 ε)))
    (hbound : ∀ z ∈ Metric.ball (0 : ℂ) ε, c ≤ ψ z ∧ ψ z ≤ C) :
    IntegrableOn (fun z : ℂ => ψ z * ‖z‖ ^ a) (Metric.ball 0 ε) ↔
      IntegrableOn (fun z : ℂ => ‖z‖ ^ a) (Metric.ball 0 ε) := by
  have hf : AEStronglyMeasurable (fun z : ℂ => ‖z‖ ^ a)
      (volume.restrict (Metric.ball 0 ε)) :=
    (continuous_norm.measurable.pow_const a).aestronglyMeasurable
  constructor
  · intro h
    apply (h.norm.const_mul (1 / c)).mono' hf
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    have hp : 0 ≤ ψ z := hc.le.trans (hbound z hz).1
    have hn : 0 ≤ ‖z‖ ^ a := Real.rpow_nonneg (norm_nonneg z) a
    rw [Real.norm_eq_abs, abs_of_nonneg hn, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hp hn)]
    calc
      ‖z‖ ^ a ≤ (ψ z * ‖z‖ ^ a) / c := by
        apply (le_div_iff₀ hc).2
        nlinarith [(hbound z hz).1, hn]
      _ = 1 / c * (ψ z * ‖z‖ ^ a) := by ring
  · intro h
    apply (h.const_mul C).mono' (hψ.mul hf)
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    have hp : 0 ≤ ψ z := hc.le.trans (hbound z hz).1
    have hn : 0 ≤ ‖z‖ ^ a := Real.rpow_nonneg (norm_nonneg z) a
    change ‖ψ z * ‖z‖ ^ a‖ ≤ C * ‖z‖ ^ a
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp hn)]
    exact mul_le_mul_of_nonneg_right (hbound z hz).2 hn

/-- The integer threshold survives a bounded positive measurable factor. -/
theorem complex_disc_mul_integrability_iff (k m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (ψ : ℂ → ℝ) (c C : ℝ) (hc : 0 < c)
    (hψ : AEStronglyMeasurable ψ (volume.restrict (Metric.ball 0 ε)))
    (hbound : ∀ z ∈ Metric.ball (0 : ℂ) ε, c ≤ ψ z ∧ ψ z ≤ C) :
    IntegrableOn (fun z : ℂ => ψ z * ‖z‖ ^ (2 * (k : ℝ) - (m : ℝ)))
      (Metric.ball 0 ε) ↔ m / 2 ≤ k := by
  rw [complex_disc_rpow_mul_integrable_iff _ ε ψ c C hc hψ hbound]
  exact complex_disc_integrability_iff k m ε hε

/-- A continuous real factor positive at the origin preserves the threshold on every
sufficiently small disc. In particular this applies to smooth positive metric factors. -/
theorem continuous_positive_local_integrability_iff (ψ : ℂ → ℝ) (hψ : Continuous ψ)
    (hψ0 : 0 < ψ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ ≤ ε → ∀ k m : ℕ,
      (IntegrableOn (fun z : ℂ => ψ z * ‖z‖ ^ (2 * (k : ℝ) - (m : ℝ)))
        (Metric.ball 0 δ) ↔ m / 2 ≤ k) := by
  have hev : ∀ᶠ z : ℂ in nhds 0, ψ 0 / 2 < ψ z ∧ ψ z < 2 * ψ 0 :=
    hψ.continuousAt (Ioo_mem_nhds (by linarith) (by linarith))
  obtain ⟨ε, hε, hbounds⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε, hε, ?_⟩
  intro δ hδ hδε k m
  apply complex_disc_mul_integrability_iff k m δ hδ ψ
    (ψ 0 / 2) (2 * ψ 0) (by positivity) hψ.measurable.aestronglyMeasurable
  intro z hz
  have hzε : dist z 0 < ε := lt_of_lt_of_le hz hδε
  exact ⟨(hbounds hzε).1.le, (hbounds hzε).2.le⟩

/-- A continuous complex factor nonzero at the origin does not change the threshold on
all sufficiently small discs. This explicitly supplies the local unit-factor bridge. -/
theorem continuous_unit_local_integrability_iff (g : ℂ → ℂ) (hg : Continuous g)
    (hg0 : g 0 ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ ≤ ε → ∀ k m : ℕ,
      (IntegrableOn (fun z : ℂ => ‖g z‖ ^ 2 * ‖z‖ ^ (2 * (k : ℝ) - (m : ℝ)))
        (Metric.ball 0 δ) ↔ m / 2 ≤ k) :=
  continuous_positive_local_integrability_iff (fun z => ‖g z‖ ^ 2) (hg.norm.pow 2)
    (pow_pos (norm_pos_iff.mpr hg0) 2)

/-- Both the smooth positive metric factor and a nonvanishing continuous unit factor
may be included simultaneously in the normal-coordinate integral. -/
theorem continuous_positive_unit_local_integrability_iff (ψ : ℂ → ℝ) (hψ : Continuous ψ)
    (hψ0 : 0 < ψ 0) (g : ℂ → ℂ) (hg : Continuous g) (hg0 : g 0 ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ ≤ ε → ∀ k m : ℕ,
      (IntegrableOn (fun z : ℂ => (ψ z * ‖g z‖ ^ 2) *
        ‖z‖ ^ (2 * (k : ℝ) - (m : ℝ))) (Metric.ball 0 δ) ↔ m / 2 ≤ k) :=
  continuous_positive_local_integrability_iff (fun z => ψ z * ‖g z‖ ^ 2)
    (hψ.mul (hg.norm.pow 2)) (mul_pos hψ0 (pow_pos (norm_pos_iff.mpr hg0) 2))

end FailureOfSemipositiveMetricExtension
