import FailureOfSemipositiveMetricExtension.ComplexIntegrability

/-!
The local product-coordinate analytic step in complex dimension two. The first coordinate
is normal to the divisor and the second is tangential. These theorems concern Lebesgue
integrability on actual polydiscs; no germ, divisibility, or sheaf assertion is encoded.
-/

open MeasureTheory Set
open scoped ENNReal

namespace FailureOfSemipositiveMetricExtension

/-- Tonelli reduction of a normal-coordinate power on a complex polydisc. -/
theorem complex_polydisc_rpow_lintegral (a ε δ : ℝ) :
    (∫⁻ p : ℂ × ℂ in Metric.ball 0 ε ×ˢ Metric.ball 0 δ,
      ENNReal.ofReal (‖p.1‖ ^ a)) =
      (∫⁻ z : ℂ in Metric.ball 0 ε, ENNReal.ofReal (‖z‖ ^ a)) *
        volume (Metric.ball (0 : ℂ) δ) := by
  rw [Measure.volume_eq_prod, setLIntegral_prod]
  · simp only [lintegral_const, Measure.restrict_apply_univ]
    exact lintegral_mul_const' _ _ measure_ball_lt_top.ne
  · fun_prop

/-- A tangential disc of positive radius contributes only a positive finite area factor. -/
theorem complex_polydisc_rpow_integrable_iff (a ε δ : ℝ) (hδ : 0 < δ) :
    IntegrableOn (fun p : ℂ × ℂ => ‖p.1‖ ^ a)
      (Metric.ball 0 ε ×ˢ Metric.ball 0 δ) ↔
      IntegrableOn (fun z : ℂ => ‖z‖ ^ a) (Metric.ball 0 ε) := by
  have hmP : AEStronglyMeasurable (fun p : ℂ × ℂ => ‖p.1‖ ^ a)
      (volume.restrict (Metric.ball 0 ε ×ˢ Metric.ball 0 δ)) :=
    (measurable_fst.norm.pow_const a).aestronglyMeasurable
  have hmC : AEStronglyMeasurable (fun z : ℂ => ‖z‖ ^ a)
      (volume.restrict (Metric.ball 0 ε)) :=
    (continuous_norm.measurable.pow_const a).aestronglyMeasurable
  have hposP : 0 ≤ᵐ[volume.restrict
      (Metric.ball (0 : ℂ) ε ×ˢ Metric.ball (0 : ℂ) δ)]
      (fun p : ℂ × ℂ => ‖p.1‖ ^ a) :=
    Filter.Eventually.of_forall fun p => Real.rpow_nonneg (norm_nonneg p.1) a
  have hposC : 0 ≤ᵐ[volume.restrict (Metric.ball (0 : ℂ) ε)]
      (fun z : ℂ => ‖z‖ ^ a) :=
    Filter.Eventually.of_forall fun z => Real.rpow_nonneg (norm_nonneg z) a
  simp only [IntegrableOn, Integrable, hmP, hmC, true_and,
    hasFiniteIntegral_iff_ofReal hposP, hasFiniteIntegral_iff_ofReal hposC]
  rw [complex_polydisc_rpow_lintegral]
  have harea : volume (Metric.ball (0 : ℂ) δ) ≠ 0 :=
    ne_of_gt (Metric.measure_ball_pos volume 0 hδ)
  exact ⟨fun h => ENNReal.lt_top_of_mul_ne_top_left h.ne harea,
    fun h => ENNReal.mul_lt_top h measure_ball_lt_top⟩

/-- The exact integer threshold on a complex surface coordinate polydisc. -/
theorem complex_polydisc_integrability_iff (k m : ℕ) (ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) :
    IntegrableOn (fun p : ℂ × ℂ => ‖p.1‖ ^ (2 * (k : ℝ) - (m : ℝ)))
      (Metric.ball 0 ε ×ˢ Metric.ball 0 δ) ↔ m / 2 ≤ k := by
  rw [complex_polydisc_rpow_integrable_iff _ ε δ hδ]
  exact complex_disc_integrability_iff k m ε hε

/-- Multiplication by a positive measurable factor with two-sided bounds preserves
integrability of a nonnegative measurable function, for an arbitrary measure. -/
theorem integrable_mul_iff_of_positive_bounds {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f ψ : α → ℝ) (c C : ℝ) (hc : 0 < c)
    (hf : AEStronglyMeasurable f μ) (hψ : AEStronglyMeasurable ψ μ)
    (hfpos : 0 ≤ᵐ[μ] f) (hbound : ∀ᵐ x ∂μ, c ≤ ψ x ∧ ψ x ≤ C) :
    Integrable (fun x => ψ x * f x) μ ↔ Integrable f μ := by
  constructor
  · intro h
    apply (h.norm.const_mul (1 / c)).mono' hf
    filter_upwards [hfpos, hbound] with x hx hb
    have hp : 0 ≤ ψ x := hc.le.trans hb.1
    rw [Real.norm_eq_abs, abs_of_nonneg hx, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hp hx)]
    calc
      f x ≤ (ψ x * f x) / c := by
        apply (le_div_iff₀ hc).2
        simpa [mul_comm] using mul_le_mul_of_nonneg_right hb.1 hx
      _ = 1 / c * (ψ x * f x) := by ring
  · intro h
    apply (h.const_mul C).mono' (hψ.mul hf)
    filter_upwards [hfpos, hbound] with x hx hb
    have hp : 0 ≤ ψ x := hc.le.trans hb.1
    change ‖ψ x * f x‖ ≤ C * f x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp hx)]
    exact mul_le_mul_of_nonneg_right hb.2 hx

/-- A bounded positive factor does not alter the surface-coordinate threshold. -/
theorem complex_polydisc_mul_integrability_iff (k m : ℕ) (ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (ψ : ℂ × ℂ → ℝ) (c C : ℝ) (hc : 0 < c)
    (hψ : AEStronglyMeasurable ψ
      (volume.restrict (Metric.ball 0 ε ×ˢ Metric.ball 0 δ)))
    (hbound : ∀ p ∈ Metric.ball (0 : ℂ) ε ×ˢ Metric.ball (0 : ℂ) δ,
      c ≤ ψ p ∧ ψ p ≤ C) :
    IntegrableOn (fun p : ℂ × ℂ => ψ p * ‖p.1‖ ^ (2 * (k : ℝ) - (m : ℝ)))
      (Metric.ball 0 ε ×ˢ Metric.ball 0 δ) ↔ m / 2 ≤ k := by
  have hmul := integrable_mul_iff_of_positive_bounds
    (volume.restrict (Metric.ball 0 ε ×ˢ Metric.ball 0 δ))
    (fun p : ℂ × ℂ => ‖p.1‖ ^ (2 * (k : ℝ) - (m : ℝ))) ψ c C hc
    (measurable_fst.norm.pow_const _).aestronglyMeasurable hψ
    (Filter.Eventually.of_forall fun p => Real.rpow_nonneg (norm_nonneg p.1) _) ?_
  · exact hmul.trans (complex_polydisc_integrability_iff k m ε δ hε hδ)
  · filter_upwards [ae_restrict_mem (measurableSet_ball.prod measurableSet_ball)] with p hp
    exact hbound p hp

/-- Any continuous factor positive at the origin preserves the threshold on all
sufficiently small complex polydiscs, with independent normal and tangent radii. -/
theorem continuous_positive_polydisc_local_integrability_iff (ψ : ℂ × ℂ → ℝ)
    (hψ : Continuous ψ) (hψ0 : 0 < ψ (0, 0)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r s : ℝ, 0 < r → 0 < s → r ≤ ε → s ≤ ε → ∀ k m : ℕ,
      (IntegrableOn (fun p : ℂ × ℂ => ψ p * ‖p.1‖ ^ (2 * (k : ℝ) - (m : ℝ)))
        (Metric.ball 0 r ×ˢ Metric.ball 0 s) ↔ m / 2 ≤ k) := by
  have hev : ∀ᶠ p : ℂ × ℂ in nhds (0, 0),
      ψ (0, 0) / 2 < ψ p ∧ ψ p < 2 * ψ (0, 0) :=
    hψ.continuousAt (Ioo_mem_nhds (by linarith) (by linarith))
  obtain ⟨ε, hε, hbounds⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε, hε, ?_⟩
  intro r s hr hs hrε hsε k m
  apply complex_polydisc_mul_integrability_iff k m r s hr hs ψ
    (ψ (0, 0) / 2) (2 * ψ (0, 0)) (by positivity) hψ.measurable.aestronglyMeasurable
  intro p hp
  have hdist : dist p (0, 0) < ε := by
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨lt_of_lt_of_le hp.1 hrε, lt_of_lt_of_le hp.2 hsε⟩
  exact ⟨(hbounds hdist).1.le, (hbounds hdist).2.le⟩

/-- A nonvanishing continuous complex unit is harmless in complex surface coordinates. -/
theorem continuous_unit_polydisc_local_integrability_iff (g : ℂ × ℂ → ℂ)
    (hg : Continuous g) (hg0 : g (0, 0) ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r s : ℝ, 0 < r → 0 < s → r ≤ ε → s ≤ ε → ∀ k m : ℕ,
      (IntegrableOn (fun p : ℂ × ℂ => ‖g p‖ ^ 2 *
        ‖p.1‖ ^ (2 * (k : ℝ) - (m : ℝ)))
        (Metric.ball 0 r ×ˢ Metric.ball 0 s) ↔ m / 2 ≤ k) :=
  continuous_positive_polydisc_local_integrability_iff
    (fun p => ‖g p‖ ^ 2) (hg.norm.pow 2) (pow_pos (norm_pos_iff.mpr hg0) 2)

/-- Continuous positive metric factors and nonvanishing unit factors are allowed together. -/
theorem continuous_positive_unit_polydisc_local_integrability_iff
    (ψ : ℂ × ℂ → ℝ) (hψ : Continuous ψ) (hψ0 : 0 < ψ (0, 0))
    (g : ℂ × ℂ → ℂ) (hg : Continuous g) (hg0 : g (0, 0) ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r s : ℝ, 0 < r → 0 < s → r ≤ ε → s ≤ ε → ∀ k m : ℕ,
      (IntegrableOn (fun p : ℂ × ℂ => (ψ p * ‖g p‖ ^ 2) *
        ‖p.1‖ ^ (2 * (k : ℝ) - (m : ℝ)))
        (Metric.ball 0 r ×ˢ Metric.ball 0 s) ↔ m / 2 ≤ k) :=
  continuous_positive_polydisc_local_integrability_iff
    (fun p => ψ p * ‖g p‖ ^ 2) (hψ.mul (hg.norm.pow 2))
    (mul_pos hψ0 (pow_pos (norm_pos_iff.mpr hg0) 2))

end FailureOfSemipositiveMetricExtension
