import FailureOfSemipositiveMetricExtension.FiberHermitianMetric
import FailureOfSemipositiveMetricExtension.CentralCubicDivision
import FailureOfSemipositiveMetricExtension.GlobalPencilGeneration

/-! Actual smooth Hermitian metrics constructed from the proved generating
sections. The remaining curvature calculation is not part of these statements. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set
open scoped Manifold ContDiff

/-- Smooth positive Hermitian metric on the actual central A-bundle. -/
def centralAMetric : SmoothHermitianMetric 0 (-2) centralADegree :=
  generatedMetric liftedCentralCubics liftedCentralCubics_basepoint_free

/-- Smooth positive Hermitian metric on the actual nearby L-bundle. -/
def nearbyLMetric (t : ℂ) (ht : t ≠ 0) : SmoothHermitianMetric t (-2) (fun _ => 1) :=
  generatedMetric (FailureOfSemipositiveMetricExtension.GlobalLineBundle.fibrePencil t)
    (FailureOfSemipositiveMetricExtension.GlobalLineBundle.fibrePencil_no_basepoint t ht)

theorem centralAMetric_positive (i : Index) (p : Fiber 0) (hp : p ∈ baseSet 0 i) :
    0 < centralAMetric.coefficient i p := centralAMetric.positive i p hp

theorem centralAMetric_smooth (i : Index) :
    ContMDiffOn 𝓘(ℝ,FixedFiber.Coord) 𝓘(ℝ) ω (centralAMetric.coefficient i) (baseSet 0 i) :=
  centralAMetric.smooth i

theorem nearbyLMetric_positive (t : ℂ) (ht : t ≠ 0) (i : Index) (p : Fiber t)
    (hp : p ∈ baseSet t i) : 0 < (nearbyLMetric t ht).coefficient i p :=
  (nearbyLMetric t ht).positive i p hp

theorem centralAMetric_formula (i : Index) (p : Fiber 0) :
    centralAMetric.coefficient i p =
      (∑ k : Fin 4, Complex.normSq ((liftedCentralCubics k).coefficient i p))⁻¹ := rfl

theorem nearbyLMetric_formula (t : ℂ) (ht : t ≠ 0) (i : Index) (p : Fiber t) :
    (nearbyLMetric t ht).coefficient i p =
      (∑ k : Fin 2, Complex.normSq
        ((FailureOfSemipositiveMetricExtension.GlobalLineBundle.fibrePencil t k).coefficient i p))⁻¹ := rfl

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
