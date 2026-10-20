import FailureOfSemipositiveMetricExtension.ExtendedWeightComparison
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! Genuine germ integrability is preserved by the one-sided extended-weight
comparison used by the nonextension argument. -/
namespace FailureOfSemipositiveMetricExtension.Multiplier
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal

variable (M : Type) [TopologicalSpace M] [ChartedSpace Coord M]

theorem IntegrableGerm.mono_of_comparison (m : ℕ) (u v : M → WithBot ℝ)
    (p : M) (g : Stalk M p) (C : ℝ)
    (hcmp : ∀ x, v x + ((-C : ℝ) : WithBot ℝ) ≤ u x)
    (hv : IntegrableGerm M m v p g) : IntegrableGerm M m u p g := by
  obtain ⟨U,hp,f,hg,e,he,ε,hε,hball,hint⟩ := hv
  refine ⟨U,hp,f,hg,e,he,ε,hε,hball,?_⟩
  calc
    _ ≤ ∫⁻ z in Metric.closedBall (e.chart p) ε,
        ENNReal.ofReal (Real.exp C)^m *
          (ENNReal.ofReal (Complex.normSq (sectionFunction M U f (e.chart.symm z))) *
            exponentialWeight (v (e.chart.symm z))^m) ∂volume :=
      lintegral_mono (fun z => weightedDensity_le_of_comparison _ m _ _ C (hcmp _))
    _ = ENNReal.ofReal (Real.exp C)^m *
        ∫⁻ z in Metric.closedBall (e.chart p) ε,
          ENNReal.ofReal (Complex.normSq (sectionFunction M U f (e.chart.symm z))) *
            exponentialWeight (v (e.chart.symm z))^m ∂volume :=
      lintegral_const_mul' _ _ (by simp)
    _ < ⊤ := ENNReal.mul_lt_top (by simp) hint

/-- The comparison need hold only on an open neighbourhood of the germ point. -/
theorem IntegrableGerm.mono_of_local_comparison (m : ℕ) (u v : M → WithBot ℝ)
    (p : M) (g : Stalk M p) (C : ℝ) (V : Opens M) (hpV : p ∈ V)
    (hcmp : ∀ x ∈ V, v x + ((-C : ℝ) : WithBot ℝ) ≤ u x)
    (hv : IntegrableGerm M m v p g) : IntegrableGerm M m u p g := by
  obtain ⟨U,hp,f,hg,e,he,ε,hε,hball,hint⟩ := hv
  have hO := e.chart.isOpen_inter_preimage_symm V.2
  have hep : e.chart p ∈ e.chart.target ∩ e.chart.symm ⁻¹' (V : Set M) := by
    refine ⟨e.chart.map_source he,?_⟩
    change e.chart.symm (e.chart p) ∈ V
    rw [e.chart.left_inv he]
    exact hpV
  obtain ⟨δ,hδ,hδV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hO.mem_nhds hep)
  have hρε : Metric.closedBall (e.chart p) (min ε δ) ⊆ Metric.closedBall (e.chart p) ε :=
    Metric.closedBall_subset_closedBall (min_le_left _ _)
  have hρδ : Metric.closedBall (e.chart p) (min ε δ) ⊆ Metric.closedBall (e.chart p) δ :=
    Metric.closedBall_subset_closedBall (min_le_right _ _)
  refine ⟨U,hp,f,hg,e,he,min ε δ,lt_min hε hδ,(fun z hz => hball (hρε hz)),?_⟩
  have hintρ : (∫⁻ z in Metric.closedBall (e.chart p) (min ε δ),
      ENNReal.ofReal (Complex.normSq (sectionFunction M U f (e.chart.symm z))) *
        exponentialWeight (v (e.chart.symm z)) ^ m ∂volume) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono_set hρε) hint
  calc
    _ ≤ ∫⁻ z in Metric.closedBall (e.chart p) (min ε δ),
        ENNReal.ofReal (Real.exp C)^m *
          (ENNReal.ofReal (Complex.normSq (sectionFunction M U f (e.chart.symm z))) *
            exponentialWeight (v (e.chart.symm z))^m) ∂volume := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
      exact weightedDensity_le_of_comparison _ m _ _ C (hcmp _ (hδV (hρδ hz)).2)
    _ = ENNReal.ofReal (Real.exp C)^m *
        ∫⁻ z in Metric.closedBall (e.chart p) (min ε δ),
          ENNReal.ofReal (Complex.normSq (sectionFunction M U f (e.chart.symm z))) *
            exponentialWeight (v (e.chart.symm z))^m ∂volume :=
      lintegral_const_mul' _ _ (by simp)
    _ < ⊤ := ENNReal.mul_lt_top (by simp) hintρ

end
end FailureOfSemipositiveMetricExtension.Multiplier
