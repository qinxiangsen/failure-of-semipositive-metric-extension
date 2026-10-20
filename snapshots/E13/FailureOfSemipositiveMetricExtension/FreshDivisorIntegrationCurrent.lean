import FailureOfSemipositiveMetricExtension.Literature.PoincareLelongIntegration
import FailureOfSemipositiveMetricExtension.IndependentCurrentMetricBridge

/-! The ACTUAL central ell has its true curve-integration current. All genuine
curve, reduced-equation, chart-cover and line-frame hypotheses are instantiated.
The coefficient integral and trace-area measure are retained explicitly. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.FreshCurrentBridge
noncomputable section
open Set MeasureTheory
open WeakComplexHessian PshCurvatureCurrentInterface DistributionalCurrent
open PoincareLelongIntegrationInterface

private theorem ellIntegrationCurrent_exists :
    ∃ T : PositiveCurrent actualCoordinateAtlas,
      (∀ i, T.traceMeasure i = integrationTraceMeasure
        (curveInChart actualCoordinateAtlas (NegativeCurveAdapter.line (-2) ellDegree) NegativeCurveAdapter.divisor i)
        (curveParameterDomain actualCoordinateAtlas (NegativeCurveAdapter.line (-2) ellDegree) NegativeCurveAdapter.divisor i)) ∧
      (∀ i f, IsTest (centralCurrentCoordinate i).chart.target f → ∀ j k,
        T.coefficient i j k f = integrationCoefficient
          (curveInChart actualCoordinateAtlas (NegativeCurveAdapter.line (-2) ellDegree) NegativeCurveAdapter.divisor i)
          (curveParameterDomain actualCoordinateAtlas (NegativeCurveAdapter.line (-2) ellDegree) NegativeCurveAdapter.divisor i) j k f) ∧
      (∀ i, LocallyIntegrableOn (realRepresentative (fun z =>
        (divisorWeight ellSection).weight i.1 ((centralCurrentCoordinate i).chart.symm z)))
        (centralCurrentCoordinate i).chart.target) ∧
      (∀ i, ∀ᵐ z ∂volume.restrict (centralCurrentCoordinate i).chart.target,
        (divisorWeight ellSection).weight i.1 ((centralCurrentCoordinate i).chart.symm z) ≠ ⊥) ∧
      ∀ i f, IsTest (centralCurrentCoordinate i).chart.target f → ∀ j k,
        T.coefficient i j k f = coefficient (realRepresentative (fun z =>
          (divisorWeight ellSection).weight i.1 ((centralCurrentCoordinate i).chart.symm z))) j k f := by
  exact Literature.smooth_rational_divisor_poincare_lelong_integration_translation
    (Fiber 0) CurrentIndex Index actualCoordinateAtlas
    (NegativeCurveAdapter.line (-2) ellDegree) NegativeCurveAdapter.divisor
    (fun i => i.1) (fun _ _ hp => hp.2)

def ellIntegrationCurrent : PositiveCurrent actualCoordinateAtlas :=
  Classical.choose ellIntegrationCurrent_exists

theorem ellIntegrationCurrent_trace (i : CurrentIndex) :
    ellIntegrationCurrent.traceMeasure i = integrationTraceMeasure
      (curveInChart actualCoordinateAtlas (NegativeCurveAdapter.line (-2) ellDegree) NegativeCurveAdapter.divisor i)
      (curveParameterDomain actualCoordinateAtlas (NegativeCurveAdapter.line (-2) ellDegree) NegativeCurveAdapter.divisor i) :=
  (Classical.choose_spec ellIntegrationCurrent_exists).1 i

theorem ellIntegrationCurrent_coefficient_integral (i : CurrentIndex) (f : FixedFiber.Coord → ℝ)
    (hf : IsTest (centralCurrentCoordinate i).chart.target f) (j k : Fin 2) :
    ellIntegrationCurrent.coefficient i j k f = integrationCoefficient
      (curveInChart actualCoordinateAtlas (NegativeCurveAdapter.line (-2) ellDegree) NegativeCurveAdapter.divisor i)
      (curveParameterDomain actualCoordinateAtlas (NegativeCurveAdapter.line (-2) ellDegree) NegativeCurveAdapter.divisor i) j k f :=
  (Classical.choose_spec ellIntegrationCurrent_exists).2.1 i f hf j k

theorem ellIntegrationCurrent_coefficient_hessian (i : CurrentIndex) (f : FixedFiber.Coord → ℝ)
    (hf : IsTest (centralCurrentCoordinate i).chart.target f) (j k : Fin 2) :
    ellIntegrationCurrent.coefficient i j k f = coefficient (realRepresentative (fun z =>
      (divisorWeight ellSection).weight i.1 ((centralCurrentCoordinate i).chart.symm z))) j k f :=
  (Classical.choose_spec ellIntegrationCurrent_exists).2.2.2.2 i f hf j k

theorem ellDivisorWeight_locallyIntegrable (i : CurrentIndex) :
    LocallyIntegrableOn (realRepresentative (fun z =>
      (divisorWeight ellSection).weight i.1 ((centralCurrentCoordinate i).chart.symm z)))
      (centralCurrentCoordinate i).chart.target :=
  (Classical.choose_spec ellIntegrationCurrent_exists).2.2.1 i

theorem ellDivisorWeight_finite_ae (i : CurrentIndex) :
    ∀ᵐ z ∂volume.restrict (centralCurrentCoordinate i).chart.target,
      (divisorWeight ellSection).weight i.1 ((centralCurrentCoordinate i).chart.symm z) ≠ ⊥ :=
  (Classical.choose_spec ellIntegrationCurrent_exists).2.2.2.1 i

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.FreshCurrentBridge
