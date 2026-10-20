import FailureOfSemipositiveMetricExtension.DistributionalCurrentAtlas
import FailureOfSemipositiveMetricExtension.NegativeCurveRemovalInterface

/-! Precise REVIEW CANDIDATE: Poincare--Lelong for a genuine smooth rational
zero divisor, identified with integration along its actual parametrized curve.
This file declares no axiom and is not part of the stage10 frozen root. -/
namespace FailureOfSemipositiveMetricExtension.PoincareLelongIntegrationInterface
noncomputable section
open Set MeasureTheory IsManifold
open scoped Topology ContDiff Manifold ENNReal
open WeakComplexHessian PshCurvatureCurrentInterface DistributionalCurrent
abbrev Coord := ℂ × ℂ

/-- The complex tangent of an actual parametrized curve, never a formal normal. -/
def tangent (F : ℂ → Coord) (z : ℂ) : Coord := fderiv ℂ F z 1

/-- Cofactor vector. For F(z)=(z,a*z), this is (-a,1). -/
def normal (F : ℂ → Coord) (z : ℂ) (j : Fin 2) : ℂ :=
  if j = 0 then -(tangent F z).2 else (tangent F z).1

/-- Actual curve integral coefficient in T=i sum C[j,k] dz[j] wedge dbarz[k].
The factor 1/2 is forced by i dz wedge dbarz=2 dx wedge dy. -/
def integrationCoefficient (F : ℂ → Coord) (E : Set ℂ)
    (j k : Fin 2) (f : Coord → ℝ) : ℂ :=
  (1/2:ℂ) * ∫ z in E, (f (F z):ℂ) * normal F z j * star (normal F z k)

/-- Euclidean area measure along the curve, pushed into the actual chart. -/
def integrationTraceMeasure (F : ℂ → Coord) (E : Set ℂ) : Measure Coord :=
  Measure.map F ((volume.restrict E).withDensity
    (fun z => ENNReal.ofReal (Complex.normSq (tangent F z).1 + Complex.normSq (tangent F z).2)))

variable {M A J : Type} [TopologicalSpace M] [ChartedSpace Coord M]
variable (D : CoordinateAtlas M A) (L : NegativeCurveRemovalInterface.AnalyticLine M J)
variable (s : NegativeCurveRemovalInterface.RationalSimpleDivisor L)

/-- One actual affine chart of P1 parametrizes the curve except its single
point at infinity. The integral ignores that point, of zero induced area. -/
def curveInChart (a : A) (z : ℂ) : Coord :=
  (D.coordinate a).chart (s.curve (ProjectiveLine.param 0 z))

def curveParameterDomain (a : A) : Set ℂ :=
  (fun z => s.curve (ProjectiveLine.param 0 z)) ⁻¹' (D.coordinate a).chart.source

/-- Every local equation is in its ACTUAL line frame, not a coordinate function
chosen to normalize the desired current. -/
def localDivisorWeight (frame : A → J) (a : A) (z : Coord) : WithBot ℝ :=
  NegativeCurveRemovalInterface.divisorWeight s.equation (frame a)
    ((D.coordinate a).chart.symm z)

/-- Universal smooth-divisor Poincare--Lelong and integration-current
translation. No particular metric, divisor class, family, multiplicity bound,
minimality, or nonextension conclusion occurs in this statement. -/
def IntegrationStatement : Prop :=
  ∀ (M A J : Type) [TopologicalSpace M] [ChartedSpace Coord M]
    [T2Space M] [SecondCountableTopology M] [IsManifold 𝓘(ℂ,Coord) ω M],
    ∀ (D : CoordinateAtlas M A) (L : NegativeCurveRemovalInterface.AnalyticLine M J)
      (s : NegativeCurveRemovalInterface.RationalSimpleDivisor L) (frame : A → J),
      (∀ a, (D.coordinate a).chart.source ⊆ L.core.baseSet (frame a)) →
      ∃ T : PositiveCurrent D,
        (∀ a, T.traceMeasure a = integrationTraceMeasure (curveInChart D L s a)
          (curveParameterDomain D L s a)) ∧
        (∀ a f, IsTest (D.coordinate a).chart.target f → ∀ j k,
          T.coefficient a j k f = integrationCoefficient (curveInChart D L s a)
            (curveParameterDomain D L s a) j k f) ∧
        (∀ a, LocallyIntegrableOn (realRepresentative (localDivisorWeight D L s frame a))
          (D.coordinate a).chart.target) ∧
        (∀ a, ∀ᵐ z ∂volume.restrict (D.coordinate a).chart.target,
          localDivisorWeight D L s frame a z ≠ ⊥) ∧
        ∀ a f, IsTest (D.coordinate a).chart.target f → ∀ j k,
          T.coefficient a j k f = coefficient
            (realRepresentative (localDivisorWeight D L s frame a)) j k f

end
end FailureOfSemipositiveMetricExtension.PoincareLelongIntegrationInterface
