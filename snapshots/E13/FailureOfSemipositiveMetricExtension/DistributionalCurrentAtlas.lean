import FailureOfSemipositiveMetricExtension.AtlasCurvatureCurrent

/-! Arbitrary genuine distribution-coefficient (1,1)-currents on a covering
analytic atlas. They are not defined to be Hessians of metrics or potentials.
In particular, an arbitrary positive current is an independent input object. -/
namespace FailureOfSemipositiveMetricExtension.DistributionalCurrent
noncomputable section
open Set MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
open WeakComplexHessian PshCurvatureCurrentInterface CurrentCoordinateCovariance
abbrev Coord := ℂ × ℂ

structure CoordinateAtlas (M A : Type) [TopologicalSpace M] [ChartedSpace Coord M] where
  coordinate : A → Multiplier.AnalyticCoordinate M
  cover : ∀ p : M, ∃ a, p ∈ (coordinate a).chart.source

variable {M A : Type} [TopologicalSpace M] [ChartedSpace Coord M]
namespace CoordinateAtlas

def change (D : CoordinateAtlas M A) (a b : A) : PartialHomeomorph Coord Coord :=
  (D.coordinate a).chart.symm.trans (D.coordinate b).chart

end CoordinateAtlas

abbrev CoefficientField (A : Type) := A → Fin 2 → Fin 2 → (Coord → ℝ) → ℂ

def complexExtension (C : CoefficientField A) (a : A) (j k : Fin 2) (f : Coord → ℂ) : ℂ :=
  C a j k (fun x => (f x).re) + Complex.I * C a j k (fun x => (f x).im)

/-- Finite-order continuity on every fixed compact test support. All three
orders 0,1,2 are included, so this admits order-zero positive measure coefficients. -/
def OrderAtMostTwo (C : (Coord → ℝ) → ℂ) (U : Set Coord) : Prop :=
  ∀ K, IsCompact K → K ⊆ U → ∃ B : ℝ, 0 ≤ B ∧
    ∀ f, IsTest U f → tsupport f ⊆ K → ∀ R : ℝ, 0 ≤ R →
      (∀ x ∈ K, ‖f x‖ ≤ R) → (∀ x ∈ K, ‖fderiv ℝ f x‖ ≤ R) →
      (∀ x ∈ K, ‖iteratedFDeriv ℝ 2 f x‖ ≤ R) → ‖C f‖ ≤ B*R

/-- A real closed (1,1)-current in a genuine coordinate-descent presentation.
The coefficient maps are arbitrary, with explicit test-linearity, distribution
continuity, Hermitian reality, both closedness identities and overlap law. -/
structure Current (D : CoordinateAtlas M A) where
  coefficient : CoefficientField A
  additive : ∀ a j k f g, IsTest (D.coordinate a).chart.target f →
    IsTest (D.coordinate a).chart.target g →
    coefficient a j k (f+g) = coefficient a j k f + coefficient a j k g
  homogeneous : ∀ a j k f, IsTest (D.coordinate a).chart.target f → ∀ r : ℝ,
    coefficient a j k (r • f) = (r:ℂ)*coefficient a j k f
  orderTwo : ∀ a j k, OrderAtMostTwo (coefficient a j k) (D.coordinate a).chart.target
  real : ∀ a j k f, IsTest (D.coordinate a).chart.target f →
    coefficient a k j f = star (coefficient a j k f)
  closed_holomorphic : ∀ a f, IsTest (D.coordinate a).chart.target f → ∀ l j k,
    coefficient a j k (firstDirectional (unitVector l) f) -
      Complex.I * coefficient a j k (firstDirectional (Complex.I • unitVector l) f) =
    coefficient a l k (firstDirectional (unitVector j) f) -
      Complex.I * coefficient a l k (firstDirectional (Complex.I • unitVector j) f)
  closed_antiholomorphic : ∀ a f, IsTest (D.coordinate a).chart.target f → ∀ l j k,
    coefficient a j k (firstDirectional (unitVector l) f) +
      Complex.I * coefficient a j k (firstDirectional (Complex.I • unitVector l) f) =
    coefficient a j l (firstDirectional (unitVector k) f) +
      Complex.I * coefficient a j l (firstDirectional (Complex.I • unitVector k) f)
  transported_test : ∀ a b f, IsTest (D.change a b).source f → ∀ j k r s,
    IsComplexTest (D.change a b).target (transportedTest (D.change a b) f j k r s)
  compatible : ∀ a b f, IsTest (D.change a b).source f → ∀ j k,
    coefficient a j k f = ∑ r : Fin 2, ∑ s : Fin 2,
      complexExtension coefficient b r s (transportedTest (D.change a b) f j k r s)

def Current.IsPositive {D : CoordinateAtlas M A} (T : Current D) : Prop :=
  ∀ a (v : Fin 2 → ℂ) f, IsTest (D.coordinate a).chart.target f →
    (∀ x, 0 ≤ f x) → 0 ≤ (∑ j : Fin 2, ∑ k : Fin 2,
      v j * star (v k) * T.coefficient a j k f).re

/-- The actual trace Borel measure, not a symbol for a Lelong number. -/
structure PositiveCurrent (D : CoordinateAtlas M A) extends Current D where
  positive : toCurrent.IsPositive
  traceMeasure : A → Measure Coord
  trace_outside : ∀ a, traceMeasure a (D.coordinate a).chart.targetᶜ = 0
  trace_finite_compact : ∀ a K, IsCompact K → K ⊆ (D.coordinate a).chart.target → traceMeasure a K < ⊤
  trace_pairing : ∀ a f, IsTest (D.coordinate a).chart.target f →
    (∫ x, f x ∂traceMeasure a : ℝ) = 2 * (coefficient a 0 0 f + coefficient a 1 1 f).re

def metricCoordinateAtlas (D : AtlasCurvature.MetricAtlas M A) : CoordinateAtlas M A :=
  ⟨D.coordinate,D.cover⟩

private theorem hessian_hermitian (u : Coord → ℝ) (j k : Fin 2) (f : Coord → ℝ) :
    PshCurvatureCurrentInterface.coefficient u k j f = star (PshCurvatureCurrentInterface.coefficient u j k f) := by
  fin_cases j <;> fin_cases k <;>
    simp [PshCurvatureCurrentInterface.coefficient,diagonalCoefficient,Complex.star_def]

/-- Every already constructed metric curvature yields a member of the new
independent arbitrary-current type; no existence theorem is used in this adapter. -/
def metricCurrent
    {D : AtlasCurvature.MetricAtlas M A} (T : D.GlobalPositiveClosedCurrent) :
    PositiveCurrent (metricCoordinateAtlas D) where
  coefficient a := PshCurvatureCurrentInterface.coefficient (realRepresentative (D.localWeight a))
  additive a j k f g hf hg := coefficient_add (T.localCurrent a).locallyIntegrable hf hg j k
  homogeneous a j k f hf r := coefficient_smul _ hf.1 r j k
  orderTwo a j k K hK hKU := by
    obtain ⟨B,hB,h⟩ := (T.localCurrent a).orderTwo K hK hKU
    exact ⟨B,hB,fun f hf hfK R hR _ _ h2 => h f hf hfK R hR h2 j k⟩
  real a j k f _ := hessian_hermitian _ j k f
  closed_holomorphic a := (T.localCurrent a).closed_holomorphic
  closed_antiholomorphic a := (T.localCurrent a).closed_antiholomorphic
  transported_test := T.transported_test
  compatible := T.compatible
  positive a := (T.localCurrent a).positive
  traceMeasure a := (T.localCurrent a).traceMeasure
  trace_outside a := (T.localCurrent a).trace_outside
  trace_finite_compact a := (T.localCurrent a).trace_finite_compact
  trace_pairing a f hf := by
    rw [(T.localCurrent a).trace_pairing f hf]
    have h := congrArg Complex.re (weakTrace_eq_coefficient_trace (T.localCurrent a).locallyIntegrable hf)
    simpa using h

end
end FailureOfSemipositiveMetricExtension.DistributionalCurrent
