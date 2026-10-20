import FailureOfSemipositiveMetricExtension.GeneralCanonicalNormMeasure

/-! Measurability of the genuine canonical densities follows from actual
holomorphic coefficients and the upper semicontinuity of the psh weights. -/
namespace FailureOfSemipositiveMetricExtension.GeneralCao
noncomputable section
open Set Filter Topology MeasureTheory IsManifold
open scoped Manifold ContDiff ENNReal

variable {n : ℕ} {M N : Type} [TopologicalSpace M] [ChartedSpace (Coord (n+1)) M]
    [TopologicalSpace N] [ChartedSpace (Coord n) N]
    [IsManifold 𝓘(ℂ,Coord n) ω N]
    {A B J : Type} (G : Family n M N A B) (L : AnalyticLine n (M := M) J)
    (s : CentralAdjointSection n G L) (h : SemipositiveWeight n G L)

theorem SemipositiveWeight.upperSemicontinuousOn (i : J) :
    UpperSemicontinuousOn (h.weight i) (L.core.baseSet i) := by
  intro p hp c hc
  obtain ⟨b,hpb⟩ := G.totalAtlas.cover p
  let e := G.totalAtlas.chart b
  have he : e p ∈ e.target ∩ e.symm ⁻¹' L.core.baseSet i := by
    refine ⟨e.map_source hpb,?_⟩
    change e.symm (e p) ∈ L.core.baseSet i
    rwa [e.left_inv hpb]
  have hh : ∀ᶠ z in nhdsWithin (e p) (e.target ∩ e.symm ⁻¹' L.core.baseSet i),
      h.weight i (e.symm z) < c := by
    apply (h.psh b i).1 (e p) he c
    change h.weight i (e.symm (e p)) < c
    rwa [e.left_inv hpb]
  have ho : IsOpen (e.target ∩ e.symm ⁻¹' L.core.baseSet i) :=
    e.symm.isOpen_inter_preimage (L.core.isOpen_baseSet i)
  rw [nhdsWithin_eq_nhds.mpr (ho.mem_nhds he)] at hh
  have ht := (e.continuousOn.continuousAt (e.open_source.mem_nhds hpb)).tendsto.eventually hh
  apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
  filter_upwards [ht,e.open_source.mem_nhds hpb] with q hq hqs
  simpa only [e.left_inv hqs] using hq

def centralChartFrameDomain (e : GeneralMultiplier.AnalyticCoordinate n N) (i : J) : Set (Coord n) :=
  e.chart.target ∩ e.chart.symm ⁻¹' (G.inclusion ⁻¹' L.core.baseSet i)

theorem centralChartFrameDomain_open (e : GeneralMultiplier.AnalyticCoordinate n N) (i : J) :
    IsOpen (centralChartFrameDomain G L e i) :=
  e.chart.symm.isOpen_inter_preimage ((L.core.isOpen_baseSet i).preimage G.inclusion_analytic.continuous)

theorem SemipositiveWeight.central_chart_upperSemicontinuous
    (e : GeneralMultiplier.AnalyticCoordinate n N) (i : J) :
    UpperSemicontinuousOn (fun q => h.weight i (G.inclusion (e.chart.symm q)))
      (centralChartFrameDomain G L e i) := by
  intro q hq c hc
  have hh := h.upperSemicontinuousOn G L i _ hq.2 c hc
  rw [nhdsWithin_eq_nhds.mpr ((L.core.isOpen_baseSet i).mem_nhds hq.2)] at hh
  have ht := (G.inclusion_analytic.continuous.continuousAt.comp
    (e.chart.continuousOn_symm.continuousAt (e.chart.open_target.mem_nhds hq.1))).tendsto.eventually hh
  exact ht.filter_mono nhdsWithin_le_nhds

theorem CentralAdjointSection.chartCoefficient_continuousOn
    (e : GeneralMultiplier.AnalyticCoordinate n N) (i : J) :
    ContinuousOn (fun q => s.chartCoefficient G L e i (e.chart.symm q))
      (centralChartFrameDomain G L e i) := by
  intro q hq
  obtain ⟨a,ha⟩ := G.centralAtlas.cover (e.chart.symm q)
  let U := e.chart.target ∩ e.chart.symm ⁻¹' (centralPatch n G L a i : Set N)
  have hU : IsOpen U := e.chart.symm.isOpen_inter_preimage (centralPatch n G L a i).isOpen
  have hqU : q ∈ U := ⟨hq.1,ha,hq.2⟩
  have hdom : U ⊆ e.changeDomain (G.centralCoordinate a) := fun _ hz => ⟨hz.1,hz.2.1⟩
  have hj := ((e.change_jacobian_continuousOn (G.centralCoordinate a)).mono hdom).continuousAt
    (hU.mem_nhds hqU)
  have hf := ((s.analytic a i).continuousOn.comp (e.chart.continuousOn_symm.mono inter_subset_left)
    (fun z hz => hz.2)).continuousAt (hU.mem_nhds hqU)
  have heq : (fun z => s.chartCoefficient G L e i (e.chart.symm z)) =ᶠ[nhds q]
      (fun z => GeneralComplexJacobian.jacobian (e.change (G.centralCoordinate a)) z *
        s.coefficient a i (e.chart.symm z)) := by
    filter_upwards [hU.mem_nhds hqU] with z hz
    rw [s.chartCoefficient_from_central G L a e i _ hz.2 (e.chart.map_target hz.1),
      e.chart.right_inv hz.1]
  exact ((hj.mul hf).congr_of_eventuallyEq heq).continuousWithinAt

theorem CentralAdjointSection.density_chart_measurable
    (e : GeneralMultiplier.AnalyticCoordinate n N) (i : J) :
    Measurable (fun q : centralChartFrameDomain G L e i =>
      s.density G L h e i (e.chart.symm q)) := by
  have hc := (continuousOn_iff_continuous_restrict.mp (s.chartCoefficient_continuousOn G L e i)).measurable
  have hn := (Complex.continuous_normSq.measurable.comp hc).ennreal_ofReal
  have hw := Multiplier.exponentialWeight_restrict_measurable (h.central_chart_upperSemicontinuous G L e i)
  exact hn.mul hw

theorem CanonicalNormPatch.density_aemeasurable (P : CanonicalNormPatch G L s h) :
    AEMeasurable (fun q => s.density G L h P.chart P.frame (P.chart.chart.symm q))
      (volume.restrict (Metric.closedBall P.center P.radius)) := by
  have hsub : Metric.closedBall P.center P.radius ⊆ centralChartFrameDomain G L P.chart P.frame :=
    fun q hq => ⟨P.closed_subtarget hq,P.closed_frame hq⟩
  exact (aemeasurable_restrict_of_measurable_subtype
    (centralChartFrameDomain_open G L P.chart P.frame).measurableSet
    (s.density_chart_measurable G L h P.chart P.frame)).mono_set hsub

end
end FailureOfSemipositiveMetricExtension.GeneralCao
