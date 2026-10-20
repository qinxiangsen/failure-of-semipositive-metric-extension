import FailureOfSemipositiveMetricExtension.GeneralCentralChartCoefficient

/-! Actual multiplier germs imply finite canonical norm patches. The germ
representative is first identified on a common neighbourhood, then the genuine
coordinate Jacobian is bounded on a compact ball. -/
namespace FailureOfSemipositiveMetricExtension.GeneralCao
noncomputable section
open Set MeasureTheory Topology IsManifold
open scoped Manifold ContDiff ENNReal

variable {n : ℕ} {M N : Type} [TopologicalSpace M] [ChartedSpace (Coord (n+1)) M]
    [TopologicalSpace N] [ChartedSpace (Coord n) N]
    [IsManifold 𝓘(ℂ,Coord n) ω N]
    {A B J : Type} (G : Family n M N A B) (L : AnalyticLine n (M := M) J)
    (s : CentralAdjointSection n G L) (h : SemipositiveWeight n G L)

theorem canonicalNormPatch_at (hm : InRestrictedMultiplier n G L h s) (p : N) :
    ∃ P : CanonicalNormPatch G L s h, p ∈ P.openSet := by
  obtain ⟨a,hpa⟩ := G.centralAtlas.cover p
  let i := L.core.indexAt (G.inclusion p)
  have hpi : G.inclusion p ∈ L.core.baseSet i := L.core.mem_baseSet_at _
  have hp : p ∈ centralPatch n G L a i := ⟨hpa,hpi⟩
  obtain ⟨e,hpe,r,hr,hsub,hfinite⟩ := GeneralMultiplier.integrableGerm_local_representative n N 1
    (fun q => h.weight i (G.inclusion q)) (centralPatch n G L a i)
    (centralCoefficientSection n G L s a i) p hp (hm a i p hp)
  let c := G.centralCoordinate a
  have hdom : Metric.closedBall (e.chart p) r ⊆ e.changeDomain c :=
    fun q hq => ⟨(hsub hq).1,(hsub hq).2.1⟩
  have hcont : ContinuousOn (fun q => Complex.normSq (GeneralComplexJacobian.jacobian (e.change c) q))
      (Metric.closedBall (e.chart p) r) :=
    Complex.continuous_normSq.comp_continuousOn ((e.change_jacobian_continuousOn c).mono hdom)
  obtain ⟨C,hC⟩ := (isCompact_closedBall (e.chart p) r).bddAbove_image hcont
  have hbound : ∀ q ∈ Metric.closedBall (e.chart p) r,
      Complex.normSq (GeneralComplexJacobian.jacobian (e.change c) q) ≤ C :=
    fun q hq => hC (mem_image_of_mem _ hq)
  have heq : ∀ q ∈ Metric.closedBall (e.chart p) r,
      s.density G L h e i (e.chart.symm q) =
        ENNReal.ofReal (Complex.normSq (GeneralComplexJacobian.jacobian (e.change c) q)) *
          (ENNReal.ofReal (Complex.normSq
            (GeneralMultiplier.sectionFunction n N (centralPatch n G L a i)
              (centralCoefficientSection n G L s a i) (e.chart.symm q))) *
            Multiplier.exponentialWeight (h.weight i (G.inclusion (e.chart.symm q))) ^ 1) := by
    intro q hq
    rw [s.density_from_central G L h a e i _ (hsub hq).2 (e.chart.map_target (hsub hq).1),
      e.chart.right_inv (hsub hq).1,
      GeneralMultiplier.sectionFunction_of_mem _ _ _ _ _ (hsub hq).2,pow_one]
    rfl
  have hnorm : (∫⁻ q in Metric.closedBall (e.chart p) r,
      s.density G L h e i (e.chart.symm q)) < ⊤ := by
    have hle : (∫⁻ q in Metric.closedBall (e.chart p) r,
        s.density G L h e i (e.chart.symm q)) ≤
      ∫⁻ q in Metric.closedBall (e.chart p) r, ENNReal.ofReal C *
          (ENNReal.ofReal (Complex.normSq
            (GeneralMultiplier.sectionFunction n N (centralPatch n G L a i)
              (centralCoefficientSection n G L s a i) (e.chart.symm q))) *
            Multiplier.exponentialWeight (h.weight i (G.inclusion (e.chart.symm q))) ^ 1) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with q hq
      rw [heq q hq]
      exact mul_le_mul_right' (ENNReal.ofReal_le_ofReal (hbound q hq)) _
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hle
    exact hle.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfinite)
  let P : CanonicalNormPatch G L s h :=
    ⟨e,i,e.chart p,r,hr,fun q hq => (hsub hq).1,fun q hq => (hsub hq).2.2,hnorm⟩
  exact ⟨P,hpe,Metric.mem_ball_self hr⟩

end
end FailureOfSemipositiveMetricExtension.GeneralCao
