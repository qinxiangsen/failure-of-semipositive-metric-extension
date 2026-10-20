import FailureOfSemipositiveMetricExtension.PlurisubharmonicRestriction
import FailureOfSemipositiveMetricExtension.CentralAuxiliaryZeroSets

/-! The original one-sided bound gives a well-defined restricted metric on every
connected component, without assuming connectedness of the central surface. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Topology

/-- The actual complement of ell is dense in the original central surface. -/
theorem ell_nonzero_dense : Dense {p : Fiber 0 | sectionValue ellSection p ≠ 0} := by
  have hd : Dense {q : FixedFiber.Coord | q.2 ≠ 0} :=
    (dense_compl_singleton (0 : ℂ)).preimage isOpenMap_snd
  apply dense_iff_inter_open.mpr
  intro U hU ⟨p,hp⟩
  obtain ⟨⟨r,e⟩,hc⟩ := FixedFiber.charts_cover 0 p
  let q := FixedFiber.coordinates 0 r e p
  have hq : q ∈ FixedFiber.domain 0 r e := (FixedFiber.chart 0 r e).map_source hc
  have heq : FixedFiber.param 0 r e q = p := FixedFiber.param_coordinates 0 r e p hc
  have ho : IsOpen (FixedFiber.domain 0 r e ∩ FixedFiber.param 0 r e ⁻¹' U) :=
    (FixedFiber.param_continuousOn 0 r e).isOpen_inter_preimage (FixedFiber.domain_isOpen 0 r e) hU
  obtain ⟨q',hq',hneq⟩ := hd.inter_open_nonempty _ ho
    ⟨q,hq,by change FixedFiber.param 0 r e q ∈ U; rwa [heq]⟩
  refine ⟨FixedFiber.param 0 r e q',hq'.2,?_⟩
  intro hz
  exact hneq ((ellSection_zero_iff_param r e q' hq'.1).mp hz).2.2

theorem centralH0_ne_bot_off_ell (i : Index) (p : Fiber 0)
    (hi : p ∈ baseSet 0 i) (hn : sectionValue ellSection p ≠ 0) : centralH0.weight i p ≠ ⊥ := by
  have hc : ellSection.coefficient i p ≠ 0 :=
    fun h => hn ((sectionValue_zero_iff ellSection i p hi).mpr h)
  simp [centralH0,hc]

theorem ell_nonzero_in_every_component (p : Fiber 0) :
    ∃ q ∈ connectedComponent p, sectionValue ellSection q ≠ 0 := by
  letI : LocallyConnectedSpace (Fiber 0) := ChartedSpace.locallyConnectedSpace FixedFiber.Coord (Fiber 0)
  exact ell_nonzero_dense.inter_open_nonempty _ isOpen_connectedComponent ⟨p,mem_connectedComponent⟩

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle

namespace FailureOfSemipositiveMetricExtension.GlobalLineBundle
noncomputable section
open Set TopologicalSpace

/-- Stronger than existence of just one finite point: no central component has
identically minus-infinite restricted weights. -/
theorem SingularWeightOn.centralDominatesH0_component_finite {U : Opens GlobalIncidence.Total}
    (h : SingularWeightOn U (-2) (fun _ => 1)) (hcomp : h.centralDominatesH0)
    (p : GlobalIncidence.Fiber 0) :
    ∃ q ∈ connectedComponent p, ∃ i : Index,
      q ∈ GlobalIncidence.FixedFiberBundle.baseSet 0 i ∧
        h.weight i (GlobalIncidence.FixedFiber.inclusion 0 q) ≠ ⊥ := by
  obtain ⟨q,hq,hn⟩ := GlobalIncidence.FixedFiberBundle.ell_nonzero_in_every_component p
  let i := (GlobalIncidence.FixedFiberBundle.core 0 (-2) (fun _ => 1)).indexAt q
  have hi : q ∈ GlobalIncidence.FixedFiberBundle.baseSet 0 i :=
    (GlobalIncidence.FixedFiberBundle.core 0 (-2) (fun _ => 1)).mem_baseSet_at q
  refine ⟨q,hq,i,hi,?_⟩
  obtain ⟨C,hC⟩ := hcomp
  have hb := hC i q hi
  have hn0 := GlobalIncidence.FixedFiberBundle.centralH0_ne_bot_off_ell i q hi hn
  intro he
  rw [he] at hb
  have hz := le_bot_iff.mp hb
  simpa [hn0] using hz

end
end FailureOfSemipositiveMetricExtension.GlobalLineBundle
