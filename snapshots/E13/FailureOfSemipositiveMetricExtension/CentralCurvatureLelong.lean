import FailureOfSemipositiveMetricExtension.CentralCurvatureCurrentAdapter
import FailureOfSemipositiveMetricExtension.Literature.PshCurvatureLelong

/-! Concrete application to the original h0, with all psh, nondegeneracy,
chart-domain and logarithmic-growth hypotheses proved in the actual family. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open FailureOfSemipositiveMetricExtension.PshCurvatureCurrentInterface

theorem centralH0_curvatureCurrent (i : Index) (r : Fin 4) (e : Fin 2) :
    ∃ T : CurvatureCurrent
      (fun q => centralH0.weight i (FixedFiber.param 0 r e q)) (weightChartDomain 0 i r e),
      ∀ q ∈ weightChartDomain 0 i r e,
        HasLelongNumber T q (FailureOfSemipositiveMetricExtension.logarithmicOrder
          (fun z => centralH0.weight i (FixedFiber.param 0 r e z)) q) :=
  centralH0_curvatureCurrent_of_pshCurrentStatement
    FailureOfSemipositiveMetricExtension.Literature.psh_curvature_current_lelong_via_distribution_translation i r e

/-- Actual local closed positive curvature current at every point of ell, whose
Euclidean trace-mass ratio tends to 1/2. -/
theorem centralH0_current_lelong_half
    (p : Fiber 0) (hz : sectionValue ellSection p = 0) :
    ∃ d : DivisionIndex, p ∈ divisionPatch 0 d ∧
      ∃ T : CurvatureCurrent
        (fun q => centralH0.weight (divisionFrame d) (FixedFiber.param 0 d.1 d.2.1 q))
        (weightChartDomain 0 (divisionFrame d) d.1 d.2.1),
        HasLelongNumber T (FixedFiber.coordinates 0 d.1 d.2.1 p) (1/2) :=
  centralH0_current_lelong_half_of_pshCurrentStatement
    FailureOfSemipositiveMetricExtension.Literature.psh_curvature_current_lelong_via_distribution_translation p hz

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
