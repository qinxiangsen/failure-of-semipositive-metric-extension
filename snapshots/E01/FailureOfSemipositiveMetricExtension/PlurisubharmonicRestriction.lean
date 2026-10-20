import FailureOfSemipositiveMetricExtension.GlobalSingularWeights
import FailureOfSemipositiveMetricExtension.ExtendedWeightMeasurability

/-! The actual central restriction of a psh metric has psh chart weights.
The proof uses the literal affine-disc definition, not a literature axiom. -/
namespace FailureOfSemipositiveMetricExtension
noncomputable section
open Set Filter Topology

theorem PlurisubharmonicOn.comp_complexLinear
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {u : F → WithBot ℝ} {U : Set F} {V : Set E}
    (hu : PlurisubharmonicOn u U) (hU : IsOpen U)
    (L : E →L[ℂ] F) (hmap : MapsTo L V U) :
    PlurisubharmonicOn (fun q => u (L q)) V := by
  constructor
  · intro x hx c hc
    have h := hu.1 (L x) (hmap hx) c hc
    rw [nhdsWithin_eq_nhds.mpr (hU.mem_nhds (hmap hx))] at h
    exact (L.continuous.continuousAt.tendsto.eventually h).filter_mono nhdsWithin_le_nhds
  · intro x v r hr hd N
    have hdisc : ∀ z : ℂ, ‖z‖ ≤ r → L x + z • L v ∈ U := by
      intro z hz
      simpa only [map_add,map_smul] using hmap (hd z hz)
    simpa only [map_add,map_smul] using hu.2 (L x) (L v) r hr hdisc N

end
end FailureOfSemipositiveMetricExtension

namespace FailureOfSemipositiveMetricExtension.GlobalLineBundle
noncomputable section
open Set TopologicalSpace

/-- Psh restriction to the literal central slice of the actual analytic family. -/
theorem SingularWeightOn.centralRestriction_plurisubharmonic {U : Opens GlobalIncidence.Total}
    {a : ℤ} {b : Fin 4 → ℤ} (h : SingularWeightOn U a b) (hU : ContainsCentralFiber U)
    (hpsh : h.HasPlurisubharmonicWeights) :
    GlobalIncidence.FixedFiberBundle.HasPlurisubharmonicWeights (h.centralRestriction hU) := by
  intro i r e
  let L : GlobalIncidence.FixedFiber.Coord →L[ℂ] GlobalIncidence.ChartCoord :=
    (ContinuousLinearMap.id ℂ GlobalIncidence.FixedFiber.Coord).prod 0
  have hm : MapsTo L (GlobalIncidence.FixedFiberBundle.weightChartDomain 0 i r e)
      (globalWeightChartDomain U i r e) := by
    intro q hq
    change (q,(0 : ℂ)) ∈ globalWeightChartDomain U i r e
    exact ⟨hq.1,hq.2,hU (GlobalIncidence.FixedFiber.param 0 r e q)⟩
  exact (hpsh i r e).comp_complexLinear (globalWeightChartDomain_isOpen U i r e) L hm

end
end FailureOfSemipositiveMetricExtension.GlobalLineBundle
