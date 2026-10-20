import FailureOfSemipositiveMetricExtension.AdjointExtendedDensity

/-! A genuine finite coordinate-ball cover of the compact central surface, with
finite actual extended weighted norms on the corresponding closed balls. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set MeasureTheory Topology TopologicalSpace
open scoped ENNReal

structure CentralNormPatch where
  frame : DivisionIndex
  center : FixedFiber.Coord
  radius : ℝ
  radius_pos : 0 < radius
  closed_subdomain : Metric.closedBall center radius ⊆ FixedFiber.domain 0 frame.1 frame.2.1
  closed_mapsTo : MapsTo (FixedFiber.param 0 frame.1 frame.2.1)
    (Metric.closedBall center radius) (divisionPatch 0 frame)

def CentralNormPatch.openSet (P : CentralNormPatch) : Set (Fiber 0) :=
  FixedFiber.source 0 P.frame.1 P.frame.2.1 ∩
    FixedFiber.coordinates 0 P.frame.1 P.frame.2.1 ⁻¹' Metric.ball P.center P.radius

theorem CentralNormPatch.isOpen (P : CentralNormPatch) : IsOpen P.openSet :=
  (FixedFiber.chart 0 P.frame.1 P.frame.2.1).isOpen_inter_preimage Metric.isOpen_ball

theorem CentralNormPatch.subset_patch (P : CentralNormPatch) : P.openSet ⊆ divisionPatch 0 P.frame := by
  intro p hp
  have hq := P.closed_mapsTo (Metric.ball_subset_closedBall hp.2)
  rwa [FixedFiber.param_coordinates 0 P.frame.1 P.frame.2.1 p hp.1] at hq

theorem centralNormPatch_cover (p : Fiber 0) : ∃ P : CentralNormPatch, p ∈ P.openSet := by
  obtain ⟨d,q,ε,hε,he,hd,hp,_⟩ := sigmaAdjointWeightedDensity_locally_integrable p
  let P : CentralNormPatch := ⟨d,q,ε,hε,hd,hp⟩
  have hq : q ∈ FixedFiber.domain 0 d.1 d.2.1 := hd (Metric.mem_closedBall_self hε.le)
  refine ⟨P,?_,?_⟩
  · rw [← he]
    exact (FixedFiber.chart 0 d.1 d.2.1).map_target hq
  · change FixedFiber.coordinates 0 d.1 d.2.1 p ∈ Metric.ball q ε
    rw [← he,FixedFiber.coordinates_param]
    exact Metric.mem_ball_self hε

theorem exists_finite_centralNormPatch_cover :
    ∃ S : Finset CentralNormPatch, ∀ p : Fiber 0, ∃ P ∈ S, p ∈ P.openSet := by
  have hcover : (univ : Set (Fiber 0)) ⊆ ⋃ P : CentralNormPatch, P.openSet := by
    intro p _
    exact mem_iUnion.mpr (centralNormPatch_cover p)
  obtain ⟨S,hS⟩ := isCompact_univ.elim_finite_subcover CentralNormPatch.openSet
    CentralNormPatch.isOpen hcover
  refine ⟨S,?_⟩
  intro p
  simpa only [mem_iUnion,exists_prop] using hS (mem_univ p)

def CentralNormPatch.normIntegral (P : CentralNormPatch) : ℝ≥0∞ :=
  ∫⁻ q in Metric.closedBall P.center P.radius,
    sigmaAdjointExtendedDensity P.frame (FixedFiber.param 0 P.frame.1 P.frame.2.1 q) ∂volume

theorem CentralNormPatch.normIntegral_lt_top (P : CentralNormPatch) : P.normIntegral < ⊤ :=
  sigmaAdjointExtendedDensity_lintegral_lt_top P.frame _ (isCompact_closedBall _ _)
    P.closed_subdomain P.closed_mapsTo

/-- The cover is finite and every actual chart integral is finite. The resulting
finite sum is a bound used for a global norm; it is not yet an assertion that an
arbitrarily patched measure is the canonical volume measure. -/
theorem finite_central_norm_cover :
    ∃ S : Finset CentralNormPatch, (∀ p : Fiber 0, ∃ P ∈ S, p ∈ P.openSet) ∧
      (∑ P ∈ S, P.normIntegral) < ⊤ := by
  obtain ⟨S,hS⟩ := exists_finite_centralNormPatch_cover
  refine ⟨S,hS,?_⟩
  exact ENNReal.sum_lt_top.mpr (fun P hP => P.normIntegral_lt_top)

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
