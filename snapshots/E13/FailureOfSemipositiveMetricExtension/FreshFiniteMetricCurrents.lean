import FailureOfSemipositiveMetricExtension.IndependentCurrentMetricBridge
/-! Genuine globally descended currents for any finite-a.e. psh metric, and
finite-a.e. residual/divisor metrics derived from the exact residual identity. -/
namespace FailureOfSemipositiveMetricExtension.PshCurvatureCurrentInterface
noncomputable section
open Set MeasureTheory

theorem finitePointsDense_of_finite_ae {u : Coord → WithBot ℝ} {U : Set Coord}
    (h : ∀ᵐ x ∂volume.restrict U, u x ≠ ⊥) : FinitePointsDense u U := by
  letI : (volume : Measure Coord).IsAddHaarMeasure := by
    change ((volume : Measure ℂ).prod (volume : Measure ℂ)).IsAddHaarMeasure
    infer_instance
  intro V hV hVU hVN
  exact Measure.exists_mem_of_measure_ne_zero_of_ae (hV.measure_pos volume hVN).ne'
    (ae_restrict_of_ae_restrict_of_subset hVU h)

end
end FailureOfSemipositiveMetricExtension.PshCurvatureCurrentInterface

namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.FreshCurrentBridge
noncomputable section
open Set MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
open WeakComplexHessian PshCurvatureCurrentInterface DistributionalCurrent

variable {a : ℤ} {b : Fin 4 → ℤ}

def finitePshMetricAtlas (h : SingularHermitianWeight 0 a b)
    (hh : HasPlurisubharmonicWeights h)
    (hfin : ∀ i : CurrentIndex, ∀ᵐ z ∂volume.restrict (centralCurrentCoordinate i).chart.target,
      h.weight i.1 ((centralCurrentCoordinate i).chart.symm z) ≠ ⊥) :
    AtlasCurvature.MetricAtlas (Fiber 0) CurrentIndex where
  coordinate := centralCurrentCoordinate
  cover := centralMetricAtlas.cover
  weight i := h.weight i.1
  gauge i j := gain 0 a b j.1 i.1
  gauge_analytic i j := (gain_contMDiffOn 0 a b j.1 i.1 ω).mono (fun _ hp => ⟨hp.2.2,hp.1.2⟩)
  gauge_nonzero i j p hp := gain_ne_zero 0 a b j.1 i.1 p ⟨hp.2.2,hp.1.2⟩
  compatible i j p hp := h.compatible j.1 i.1 p ⟨hp.2.2,hp.1.2⟩
  psh i := hh i.1 i.2.1 i.2.2
  finite_dense i := finitePointsDense_of_finite_ae (hfin i)

def finitePshCoordinateCurrent (h : SingularHermitianWeight 0 a b)
    (hh : HasPlurisubharmonicWeights h)
    (hfin : ∀ i : CurrentIndex, ∀ᵐ z ∂volume.restrict (centralCurrentCoordinate i).chart.target,
      h.weight i.1 ((centralCurrentCoordinate i).chart.symm z) ≠ ⊥) :
    (finitePshMetricAtlas h hh hfin).GlobalPositiveClosedCurrent :=
  Classical.choice ((finitePshMetricAtlas h hh hfin).globalCurrent_exists_of_local_current_and_covariance
    Literature.psh_curvature_current_lelong_via_distribution_translation
    Literature.distributional_ddc_coordinate_gauge_covariance)

def finitePshCurrent (h : SingularHermitianWeight 0 a b)
    (hh : HasPlurisubharmonicWeights h)
    (hfin : ∀ i : CurrentIndex, ∀ᵐ z ∂volume.restrict (centralCurrentCoordinate i).chart.target,
      h.weight i.1 ((centralCurrentCoordinate i).chart.symm z) ≠ ⊥) :
    PositiveCurrent actualCoordinateAtlas := metricCurrent (D := finitePshMetricAtlas h hh hfin) (finitePshCoordinateCurrent h hh hfin)

@[simp] theorem finitePshCurrent_coefficient (h : SingularHermitianWeight 0 a b)
    (hh : HasPlurisubharmonicWeights h)
    (hfin : ∀ i : CurrentIndex, ∀ᵐ z ∂volume.restrict (centralCurrentCoordinate i).chart.target,
      h.weight i.1 ((centralCurrentCoordinate i).chart.symm z) ≠ ⊥)
    (i : CurrentIndex) (j k : Fin 2) (f : FixedFiber.Coord → ℝ) :
    (finitePshCurrent h hh hfin).coefficient i j k f = coefficient
      (realRepresentative (fun z => h.weight i.1 ((centralCurrentCoordinate i).chart.symm z))) j k f := rfl

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.FreshCurrentBridge
