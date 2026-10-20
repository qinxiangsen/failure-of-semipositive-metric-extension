import FailureOfSemipositiveMetricExtension.GeneralCanonicalDensityTransition
import FailureOfSemipositiveMetricExtension.FiniteMeasureGluing

/-! Genuine finite coordinate measures for arbitrary-dimensional canonical
forms. Local finiteness is explicit data, later obtained from the actual germs. -/
namespace FailureOfSemipositiveMetricExtension.GeneralCao
noncomputable section
open Set MeasureTheory Topology
open scoped Manifold ContDiff ENNReal

variable {n : ℕ} {M N : Type} [TopologicalSpace M] [ChartedSpace (Coord (n+1)) M]
    [TopologicalSpace N] [ChartedSpace (Coord n) N]
    [MeasurableSpace N] [BorelSpace N]
    [IsManifold 𝓘(ℂ,Coord n) ω N]
    {A B J : Type} (G : Family n M N A B) (L : AnalyticLine n (M := M) J)
    (s : CentralAdjointSection n G L) (h : SemipositiveWeight n G L)

structure CanonicalNormPatch where
  chart : GeneralMultiplier.AnalyticCoordinate n N
  frame : J
  center : Coord n
  radius : ℝ
  radius_pos : 0 < radius
  closed_subtarget : Metric.closedBall center radius ⊆ chart.chart.target
  closed_frame : MapsTo (G.inclusion ∘ chart.chart.symm)
    (Metric.closedBall center radius) (L.core.baseSet frame)
  norm_finite : (∫⁻ q in Metric.closedBall center radius,
    s.density G L h chart frame (chart.chart.symm q)) < ⊤

namespace CanonicalNormPatch
variable {G L s h} (P : CanonicalNormPatch G L s h)

def openSet : Set N := P.chart.chart.source ∩ P.chart.chart ⁻¹' Metric.ball P.center P.radius

theorem isOpen : IsOpen P.openSet := P.chart.chart.isOpen_inter_preimage Metric.isOpen_ball

theorem subset_frame {p : N} (hp : p ∈ P.openSet) : G.inclusion p ∈ L.core.baseSet P.frame := by
  have hf := P.closed_frame (Metric.ball_subset_closedBall hp.2)
  change G.inclusion (P.chart.chart.symm (P.chart.chart p)) ∈ _ at hf
  rwa [P.chart.chart.left_inv hp.1] at hf

def coordinateMeasure : Measure (Coord n) :=
  (volume.restrict (Metric.closedBall P.center P.radius)).withDensity
    (fun q => s.density G L h P.chart P.frame (P.chart.chart.symm q))

instance coordinateMeasure_finite : IsFiniteMeasure P.coordinateMeasure :=
  isFiniteMeasure_withDensity P.norm_finite.ne

def patchMeasure : Measure N := P.coordinateMeasure.map P.chart.chart.symm

theorem inverse_aemeasurable : AEMeasurable P.chart.chart.symm P.coordinateMeasure := by
  have hm := (P.chart.chart.continuousOn_symm.mono P.closed_subtarget).aemeasurable
    (μ := volume) measurableSet_closedBall
  exact hm.mono_ac (withDensity_absolutelyContinuous _ _)

instance patchMeasure_finite : IsFiniteMeasure P.patchMeasure := Measure.isFiniteMeasure_map _ _

theorem preimage_inter_closedBall (S : Set N) (hS : S ⊆ P.openSet) :
    P.chart.chart.symm ⁻¹' S ∩ Metric.closedBall P.center P.radius = P.chart.chart '' S := by
  ext q
  constructor
  · rintro ⟨hq,hball⟩
    exact ⟨P.chart.chart.symm q,hq,P.chart.chart.right_inv (P.closed_subtarget hball)⟩
  · rintro ⟨p,hp,rfl⟩
    refine ⟨?_,Metric.ball_subset_closedBall (hS hp).2⟩
    change P.chart.chart.symm (P.chart.chart p) ∈ S
    rwa [P.chart.chart.left_inv (hS hp).1]

theorem patchMeasure_apply (S : Set N) (hS : MeasurableSet S) (hsub : S ⊆ P.openSet) :
    P.patchMeasure S = ∫⁻ q in P.chart.chart '' S,
      s.density G L h P.chart P.frame (P.chart.chart.symm q) := by
  rw [patchMeasure,Measure.map_apply_of_aemeasurable P.inverse_aemeasurable hS,
    coordinateMeasure,withDensity_apply',Measure.restrict_restrict' measurableSet_closedBall,
    P.preimage_inter_closedBall S hsub]

theorem chart_image_measurable (S : Set N) (hS : MeasurableSet S)
    (hsub : S ⊆ P.chart.chart.source) : MeasurableSet (P.chart.chart '' S) := by
  let e := P.chart.chart
  have hm := e.isOpenEmbedding_restrict.measurableEmbedding.measurableSet_image.mpr
    (hS.preimage (measurable_subtype_coe : Measurable (fun p : e.source => (p : N))))
  have he : e.source.restrict e '' ((fun p : e.source => (p : N)) ⁻¹' S) = e '' S := by
    ext q
    constructor
    · rintro ⟨p,hp,rfl⟩; exact ⟨p,hp,rfl⟩
    · rintro ⟨p,hp,rfl⟩; exact ⟨⟨p,hsub hp⟩,hp,rfl⟩
  rwa [he] at hm

theorem measures_agree (Q : CanonicalNormPatch G L s h) (S : Set N)
    (hS : MeasurableSet S) (hP : S ⊆ P.openSet) (hQ : S ⊆ Q.openSet) :
    P.patchMeasure S = Q.patchMeasure S := by
  rw [P.patchMeasure_apply S hS hP,Q.patchMeasure_apply S hS hQ]
  have hd : S ⊆ P.chart.chart.source := fun p hp => (hP hp).1
  have ht := s.density_lintegral_change G L h P.chart Q.chart P.frame Q.frame
    (P.chart.chart '' S) (P.chart_image_measurable S hS hd)
    (by
      rintro q ⟨p,hp,rfl⟩
      refine ⟨P.chart.chart.map_source (hd hp),?_⟩
      change P.chart.chart.symm (P.chart.chart p) ∈ Q.chart.chart.source
      rw [P.chart.chart.left_inv (hd hp)]
      exact (hQ hp).1)
    (by
      rintro q ⟨p,hp,rfl⟩
      change G.inclusion (P.chart.chart.symm (P.chart.chart p)) ∈ _
      rw [P.chart.chart.left_inv (hd hp)]
      exact P.subset_frame (hP hp))
    (by
      rintro q ⟨p,hp,rfl⟩
      change G.inclusion (P.chart.chart.symm (P.chart.chart p)) ∈ _
      rw [P.chart.chart.left_inv (hd hp)]
      exact Q.subset_frame (hQ hp))
  have him : P.chart.change Q.chart '' (P.chart.chart '' S) = Q.chart.chart '' S := by
    rw [← image_comp]
    apply image_congr
    intro p hp
    change Q.chart.chart (P.chart.chart.symm (P.chart.chart p)) = _
    rw [P.chart.chart.left_inv (hd hp)]
  rw [him] at ht
  exact ht.symm

theorem restrict_measures_agree (Q : CanonicalNormPatch G L s h) :
    P.patchMeasure.restrict (P.openSet ∩ Q.openSet) = Q.patchMeasure.restrict (P.openSet ∩ Q.openSet) := by
  ext S hS
  rw [Measure.restrict_apply hS,Measure.restrict_apply hS]
  exact P.measures_agree Q _ (hS.inter (P.isOpen.measurableSet.inter Q.isOpen.measurableSet))
    (fun _ hp => hp.2.1) (fun _ hp => hp.2.2)

end CanonicalNormPatch
end
end FailureOfSemipositiveMetricExtension.GeneralCao
