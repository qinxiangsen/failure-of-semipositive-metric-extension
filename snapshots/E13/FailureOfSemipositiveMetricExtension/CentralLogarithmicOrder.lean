import FailureOfSemipositiveMetricExtension.LogarithmicOrder
import FailureOfSemipositiveMetricExtension.CentralSingularRegularity

/-! At every point of the actual singular curve, the actual h0 chart weight has
logarithmic-growth order exactly 1/2. This computes the growth characterization;
identifying it with a distributional-current Lelong number is stated separately. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Filter IsManifold
open scoped Manifold ContDiff Topology

theorem centralH0_logarithmic_order (p : Fiber 0) (hz : sectionValue ellSection p = 0) :
    ∃ d : DivisionIndex, p ∈ divisionPatch 0 d ∧
      FailureOfSemipositiveMetricExtension.logarithmicOrder
        (fun q => centralH0.weight (divisionFrame d) (FixedFiber.param 0 d.1 d.2.1 q))
        (FixedFiber.coordinates 0 d.1 d.2.1 p) = 1/2 := by
  obtain ⟨d,hp,hr,he,hform⟩ := ellSection_simple_at_zero p hz
  let q := FixedFiber.coordinates 0 d.1 d.2.1 p
  have hq : q ∈ FixedFiber.domain 0 d.1 d.2.1 := (FixedFiber.chart 0 d.1 d.2.1).map_source hp.1
  have heq : FixedFiber.param 0 d.1 d.2.1 q = p := FixedFiber.param_coordinates 0 d.1 d.2.1 p hp.1
  have hq2 : q.2 = 0 := by
    have hh := (ellSection_zero_iff_param d.1 d.2.1 q hq).mp (heq.symm ▸ hz)
    exact hh.2.2
  let V := FixedFiber.domain 0 d.1 d.2.1 ∩ FixedFiber.param 0 d.1 d.2.1 ⁻¹' divisionPatch 0 d
  have hV : IsOpen V := (FixedFiber.chart 0 d.1 d.2.1).isOpen_inter_preimage_symm (divisionPatch_isOpen 0 d)
  have hqV : q ∈ V := ⟨hq,by change FixedFiber.param 0 d.1 d.2.1 q ∈ divisionPatch 0 d; rwa [heq]⟩
  let R : FixedFiber.Coord → ℝ := fun z => centralH0RegularPart d (FixedFiber.param 0 d.1 d.2.1 z)
  have hR : ContinuousAt R q :=
    (((centralH0RegularPart_contMDiffOn d).continuousOn.comp
      ((FixedFiber.param_contMDiffOn 0 d.1 d.2.1 0).continuousOn.mono (fun _ h => h.1))
      (fun _ h => h.2)) : ContinuousOn R V).continuousAt (hV.mem_nhds hqV)
  have hevent : (fun z => centralH0.weight (divisionFrame d) (FixedFiber.param 0 d.1 d.2.1 z)) =ᶠ[𝓝 q]
      FailureOfSemipositiveMetricExtension.normalLogWeight (1/2) R := by
    filter_upwards [hV.mem_nhds hqV] with z hzV
    rw [centralH0_logarithmic_normal_form d hr he _ hzV.2,FixedFiber.coordinates_param]
    unfold FailureOfSemipositiveMetricExtension.normalLogWeight
    split_ifs
    · rfl
    · congr 1
      dsimp [R]
      ring
  refine ⟨d,hp,?_⟩
  rw [FailureOfSemipositiveMetricExtension.logarithmicOrder_congr_nhds hevent]
  have hqeq : q = (q.1,0) := by ext <;> simp [hq2]
  rw [hqeq] at hR ⊢
  exact FailureOfSemipositiveMetricExtension.normalLogWeight_order (1/2) (by norm_num) R q.1 hR

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
