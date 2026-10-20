import FailureOfSemipositiveMetricExtension.GlobalAdjointSections

/-! Actual neighbourhood shrinking and density turn vanishing of every nearby
fibre restriction into vanishing on the whole central fibre. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalAdjoint
noncomputable section
open Set Bundle IsManifold Topology TopologicalSpace
open scoped Manifold ContDiff

/-- A general continuation statement with its vanishing input explicit. The
input is discharged by the separate nearby geometric vanishing theorem. -/
theorem central_coefficient_zero_of_nearby_vanishing {U : Opens Total} {m : ℕ}
    (s : SectionOn U m) (hU : ∀ p : Fiber 0, FixedFiber.inclusion 0 p ∈ U)
    (hvan : ∀ (t : ℂ), t ≠ 0 → ∀ (v : FixedFiberBundle.AdjointSectionData t m)
      (p : Fiber t), FixedFiberBundle.adjointSectionValue v p = 0)
    (d : Index) (p : Fiber 0) (hd : p ∈ FixedFiberBundle.divisionPatch 0 d) :
    s.coefficient d (FixedFiber.inclusion 0 p) = 0 := by
  obtain ⟨ε,hε,hsub⟩ := contains_full_disc_near_zero U hU
  let W : Set Total := patch d ∩ projection ⁻¹' Metric.ball (0 : ℂ) ε
  have hopen : IsOpen W := (GlobalLineBundle.divisionPatch_isOpen d).inter
    (Metric.isOpen_ball.preimage projection_continuous)
  have hW : W ⊆ patch d ∩ U := fun _ h => ⟨h.1,hsub h.2⟩
  have hz : EqOn (s.coefficient d) (fun _ => (0 : ℂ))
      (W ∩ {q : Total | projection q ≠ 0}) := by
    intro q hq
    let t := projection q
    have ht : t ≠ 0 := hq.2
    have hfull : ∀ r : Fiber t, FixedFiber.inclusion t r ∈ U := by
      intro r
      apply hsub
      exact hq.1.2
    obtain ⟨r,hr⟩ := exists_fiber_inclusion t q rfl
    have hrp : r ∈ FixedFiberBundle.divisionPatch t d := by
      change FixedFiber.inclusion t r ∈ patch d
      rw [hr]
      exact hq.1.1
    have hv := (FixedFiberBundle.adjointSectionValue_zero_iff (restriction s t hfull) d r hrp).mp
      (hvan t ht (restriction s t hfull) r)
    simpa only [restriction_coefficient,hr] using hv
  have hzW := hz.of_subset_closure ((s.analytic d).continuousOn.mono hW) continuousOn_const
    inter_subset_left (noncentral_fibres_dense.open_subset_closure_inter hopen)
  apply hzW
  exact ⟨hd,by change dist (0 : ℂ) 0 < ε; simpa only [dist_self] using hε⟩

/-- Thus a nonzero actual central adjoint section cannot be the dt restriction
of a neighbourhood section whenever actual nearby section spaces vanish. -/
theorem no_extension_of_nearby_vanishing {U : Opens Total}
    (hU : ∀ p : Fiber 0, FixedFiber.inclusion 0 p ∈ U)
    (hvan : ∀ (t : ℂ), t ≠ 0 → ∀ (v : FixedFiberBundle.AdjointSectionData t 4)
      (p : Fiber t), FixedFiberBundle.adjointSectionValue v p = 0) :
    ¬ ∃ s : SectionOn U 4, ∀ d p, p ∈ FixedFiberBundle.divisionPatch 0 d →
      s.coefficient d (FixedFiber.inclusion 0 p) = FixedFiberBundle.sigmaAdjointCoefficient d p := by
  rintro ⟨s,hs⟩
  let p := FixedFiberBundle.auxiliaryWitness
  let d := (FixedFiberBundle.adjointCore 0 4).indexAt p
  have hd := (FixedFiberBundle.adjointCore 0 4).mem_baseSet_at p
  have hz := central_coefficient_zero_of_nearby_vanishing s hU hvan d p hd
  rw [hs d p hd] at hz
  exact FixedFiberBundle.sigmaAdjointValue_witness_ne_zero hz

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalAdjoint
