import FailureOfSemipositiveMetricExtension.ComparedCanonicalNorm
import FailureOfSemipositiveMetricExtension.PlurisubharmonicRestriction

/-! Measurability of the actual candidate weighted canonical densities follows
from the proved psh restriction, not from an implicit regularity assumption. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set MeasureTheory Topology
open scoped Manifold ContDiff ENNReal

theorem sigmaDensityForWeight_chart_measurable
    (h : SingularHermitianWeight 0 (-2) (fun _ => 1)) (hpsh : HasPlurisubharmonicWeights h)
    (d : DivisionIndex) :
    Measurable (fun q : weightChartDomain 0 (divisionFrame d) d.1 d.2.1 =>
      sigmaDensityForWeight h d (FixedFiber.param 0 d.1 d.2.1 q)) := by
  have hm : MapsTo (FixedFiber.param 0 d.1 d.2.1)
      (weightChartDomain 0 (divisionFrame d) d.1 d.2.1) (divisionPatch 0 d) :=
    fun q hq => ⟨(FixedFiber.chart 0 d.1 d.2.1).map_target hq.1,hq.2⟩
  have hc := ((sigmaAdjointCoefficient_analytic d).comp
    ((FixedFiber.param_contMDiffOn 0 d.1 d.2.1 ω).mono inter_subset_left) hm).continuousOn
  have hcm := (continuousOn_iff_continuous_restrict.mp hc).measurable
  have hn := (Complex.continuous_normSq.measurable.comp hcm).ennreal_ofReal
  have hw := Multiplier.exponentialWeight_restrict_measurable (hpsh (divisionFrame d) d.1 d.2.1).1
  exact hn.mul (hw.pow_const 4)

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
