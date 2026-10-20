import FailureOfSemipositiveMetricExtension.PshCurvatureCurrentInterface
import FailureOfSemipositiveMetricExtension.CentralLogarithmicOrder
import FailureOfSemipositiveMetricExtension.CentralRestrictionWellDefined

/-! Concrete h0 hypotheses for the explicit psh-current interface.  The universal
literature statement remains an explicit input in this module. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Filter IsManifold
open scoped Topology ContDiff Manifold
open FailureOfSemipositiveMetricExtension.PshCurvatureCurrentInterface

theorem centralH0_finitePointsDense (i : Index) (r : Fin 4) (e : Fin 2) :
    FinitePointsDense
      (fun q => centralH0.weight i (FixedFiber.param 0 r e q))
      (weightChartDomain 0 i r e) := by
  intro V hV hVU hVN
  have hd : Dense {q : FixedFiber.Coord | q.2 ≠ 0} :=
    (dense_compl_singleton (0 : ℂ)).preimage isOpenMap_snd
  obtain ⟨q,hq,hqn⟩ := hd.inter_open_nonempty V hV hVN
  have hqd := hVU hq
  refine ⟨q,hq,centralH0_ne_bot_off_ell i _ hqd.2 ?_⟩
  intro hz
  exact hqn ((ellSection_zero_iff_param r e q hqd.1).mp hz).2.2

theorem centralH0_curvatureCurrent_of_pshCurrentStatement
    (hstd : PshCurrentStatement) (i : Index) (r : Fin 4) (e : Fin 2) :
    ∃ T : CurvatureCurrent
      (fun q => centralH0.weight i (FixedFiber.param 0 r e q)) (weightChartDomain 0 i r e),
      ∀ q ∈ weightChartDomain 0 i r e,
        HasLelongNumber T q (FailureOfSemipositiveMetricExtension.logarithmicOrder
          (fun z => centralH0.weight i (FixedFiber.param 0 r e z)) q) :=
  hstd _ _ (weightChartDomain_isOpen 0 i r e) (centralH0_plurisubharmonic i r e)
    (centralH0_finitePointsDense i r e)

/-- At every actual divisor point the genuine distributional curvature has
Euclidean trace-mass Lelong number 1/2, conditional only on the universal psh
current/growth characterization stated in the separate interface. -/
theorem centralH0_current_lelong_half_of_pshCurrentStatement
    (hstd : PshCurrentStatement) (p : Fiber 0) (hz : sectionValue ellSection p = 0) :
    ∃ d : DivisionIndex, p ∈ divisionPatch 0 d ∧
      ∃ T : CurvatureCurrent
        (fun q => centralH0.weight (divisionFrame d) (FixedFiber.param 0 d.1 d.2.1 q))
        (weightChartDomain 0 (divisionFrame d) d.1 d.2.1),
        HasLelongNumber T (FixedFiber.coordinates 0 d.1 d.2.1 p) (1/2) := by
  obtain ⟨d,hp,ho⟩ := centralH0_logarithmic_order p hz
  obtain ⟨T,hT⟩ := centralH0_curvatureCurrent_of_pshCurrentStatement hstd
    (divisionFrame d) d.1 d.2.1
  refine ⟨d,hp,T,?_⟩
  have hq : FixedFiber.coordinates 0 d.1 d.2.1 p ∈
      weightChartDomain 0 (divisionFrame d) d.1 d.2.1 := by
    refine ⟨(FixedFiber.chart 0 d.1 d.2.1).map_source hp.1,?_⟩
    rw [Set.mem_preimage,FixedFiber.param_coordinates 0 d.1 d.2.1 p hp.1]
    exact hp.2
  simpa only [ho] using hT _ hq

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
