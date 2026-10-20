import FailureOfSemipositiveMetricExtension.GeneralMultiplierGerms

/-! An actual stalk integrability condition transfers to any specified local
representative on a smaller coordinate ball. No change-of-chart assertion or
finite global norm is assumed here. -/
namespace FailureOfSemipositiveMetricExtension.GeneralMultiplier
noncomputable section
open Set MeasureTheory Topology TopologicalSpace CategoryTheory Opposite Manifold
open scoped Manifold ContDiff ENNReal

variable (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (Coord n) M]

theorem integrableGerm_local_representative (m : ℕ) (w : M → WithBot ℝ)
    (U : Opens M) (f : C^∞⟮𝓘(ℂ,Coord n),U;𝓘(ℂ),ℂ⟯) (p : M) (hp : p ∈ U)
    (hg : IntegrableGerm n M m w p ((sheaf n M).presheaf.germ U p hp f)) :
    ∃ (e : AnalyticCoordinate n M), p ∈ e.chart.source ∧ ∃ r : ℝ, 0 < r ∧
      Metric.closedBall (e.chart p) r ⊆ e.chart.target ∩ e.chart.symm ⁻¹' U ∧
      (∫⁻ z in Metric.closedBall (e.chart p) r,
        ENNReal.ofReal (Complex.normSq (sectionFunction n M U f (e.chart.symm z))) *
          Multiplier.exponentialWeight (w (e.chart.symm z)) ^ m ∂volume) < ⊤ := by
  obtain ⟨V,hpV,g,hgerm,e,hpe,ε,hε,hsub,hfinite⟩ := hg
  obtain ⟨W,hpW,i,j,hW⟩ := (sheaf n M).presheaf.germ_eq p hpV hp g f hgerm
  have hWsubV : (W : Set M) ⊆ V := leOfHom i
  have hWsubU : (W : Set M) ⊆ U := leOfHom j
  have hopen : IsOpen (e.chart.target ∩ e.chart.symm ⁻¹' (W : Set M)) :=
    e.chart.symm.isOpen_inter_preimage W.isOpen
  have hmem : e.chart p ∈ e.chart.target ∩ e.chart.symm ⁻¹' (W : Set M) :=
    ⟨e.chart.map_source hpe,by change e.chart.symm (e.chart p) ∈ W; rwa [e.chart.left_inv hpe]⟩
  obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hmem)
  let r := min ε (δ / 2)
  have hr : 0 < r := lt_min hε (half_pos hδ)
  have hrε : r ≤ ε := min_le_left _ _
  have hrδ : r < δ := (min_le_right _ _).trans_lt (half_lt_self hδ)
  have hsmall : Metric.closedBall (e.chart p) r ⊆ e.chart.target ∩ e.chart.symm ⁻¹' (W : Set M) :=
    fun z hz => hδsub (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hz).trans_lt hrδ))
  refine ⟨e,hpe,r,hr,fun z hz => ⟨(hsmall hz).1,hWsubU (hsmall hz).2⟩,?_⟩
  have heq : ∀ z ∈ Metric.closedBall (e.chart p) r,
      sectionFunction n M U f (e.chart.symm z) = sectionFunction n M V g (e.chart.symm z) := by
    intro z hz
    have hq := (hsmall hz).2
    rw [sectionFunction_of_mem _ _ _ _ _ (hWsubU hq),sectionFunction_of_mem _ _ _ _ _ (hWsubV hq)]
    exact (congrArg (fun h : C^∞⟮𝓘(ℂ,Coord n),W;𝓘(ℂ),ℂ⟯ => h ⟨e.chart.symm z,hq⟩) hW).symm
  have hle : (∫⁻ z in Metric.closedBall (e.chart p) r,
        ENNReal.ofReal (Complex.normSq (sectionFunction n M U f (e.chart.symm z))) *
          Multiplier.exponentialWeight (w (e.chart.symm z)) ^ m ∂volume) ≤
      ∫⁻ z in Metric.closedBall (e.chart p) ε,
        ENNReal.ofReal (Complex.normSq (sectionFunction n M V g (e.chart.symm z))) *
          Multiplier.exponentialWeight (w (e.chart.symm z)) ^ m ∂volume := by
    calc
      _ = ∫⁻ z in Metric.closedBall (e.chart p) r,
        ENNReal.ofReal (Complex.normSq (sectionFunction n M V g (e.chart.symm z))) *
          Multiplier.exponentialWeight (w (e.chart.symm z)) ^ m ∂volume := by
            apply setLIntegral_congr_fun measurableSet_closedBall
            filter_upwards [] with z hz
            rw [heq z hz]
      _ ≤ _ := lintegral_mono_set (Metric.closedBall_subset_closedBall hrε)
  exact hle.trans_lt hfinite

end
end FailureOfSemipositiveMetricExtension.GeneralMultiplier
