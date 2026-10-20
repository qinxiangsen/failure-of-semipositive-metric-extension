import FailureOfSemipositiveMetricExtension.CurrentDeRhamClass
import FailureOfSemipositiveMetricExtension.CentralGlobalCurvatureCurrent
import FailureOfSemipositiveMetricExtension.CentralMetricMinimality

/-! A small, fresh standard-input adapter.  The current variable is an
independently given distribution current; it is NEVER defined as a metric.
The sole new analytic input is universal compact-projective dd^c + local psh
regularity, stated for arbitrary genuine line bundles and covering frame atlases.
No negative curve, special exponent, h0, or paper conclusion occurs in it.
Real c1 is presented by the curvature class of a finite-a.e. psh reference
metric.  The ordinary Chern--Weil/singular-metric comparison is the explicitly
external interpretation of this presentation; no integral c1 is constructed. -/
namespace FailureOfSemipositiveMetricExtension.IndependentCurrentMetricBridge
noncomputable section
open Set MeasureTheory IsManifold
open scoped Manifold ContDiff Topology
open WeakComplexHessian PshCurvatureCurrentInterface DistributionalCurrent
open NegativeCurveRemovalInterface
abbrev Coord := ℂ × ℂ
variable {M A J : Type} [TopologicalSpace M] [ChartedSpace Coord M]

/-- Each coordinate sits inside its named actual bundle frame; every frame
is locally covered, so psh reconstruction is not confined to a partial cover. -/
structure FrameAtlas (L : AnalyticLine M J) where
  coordinates : CoordinateAtlas M A
  frame : A → J
  source_frame : ∀ a, (coordinates.coordinate a).chart.source ⊆ L.core.baseSet (frame a)
  frame_cover : ∀ i p, p ∈ L.core.baseSet i →
    ∃ a, frame a = i ∧ p ∈ (coordinates.coordinate a).chart.source

/-- One metric represents THIS independent current, finite a.e. and on EVERY
compact test, with the normalization i/(2π)∂∂bar and squared-norm weights. -/
structure Represents {L : AnalyticLine M J} (D : FrameAtlas (A := A) L)
    (T : PositiveCurrent D.coordinates) (h : Weight L) : Prop where
  finite_ae : ∀ a, ∀ᵐ z ∂volume.restrict (D.coordinates.coordinate a).chart.target,
    h.weight (D.frame a) ((D.coordinates.coordinate a).chart.symm z) ≠ ⊥
  coefficient_eq : ∀ a f, IsTest (D.coordinates.coordinate a).chart.target f → ∀ j k,
    coefficient (realRepresentative (fun z => h.weight (D.frame a)
      ((D.coordinates.coordinate a).chart.symm z))) j k f = T.coefficient a j k f

/-- Universal statement of the compact Kähler dd^c lemma and the positive
current/psh-metric correspondence, with a singular reference metric permitted.
A finite projective immersion supplies Kählerness.  The equality of de Rham
classes is between independent genuine currents, not defined via potentials. -/
def ReconstructionStatement : Prop :=
  ∀ (M A J C : Type) [TopologicalSpace M] [ChartedSpace Coord M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [IsManifold 𝓘(ℂ,Coord) ω M],
    ∀ (atlas : CaoExtensionInterface.AnalyticAtlas Coord M C),
    ProjectiveImmersion (M := M) →
    ∀ (L : AnalyticLine M J) (D : FrameAtlas (A := A) L)
      (hRef : Weight L), IsPsh atlas hRef →
    ∀ (S T : PositiveCurrent D.coordinates), Represents D S hRef →
      deRhamClass T.toCurrent = deRhamClass S.toCurrent →
      ∃ h : Weight L, IsPsh atlas h ∧ Represents D T h

end
end FailureOfSemipositiveMetricExtension.IndependentCurrentMetricBridge

namespace FailureOfSemipositiveMetricExtension.Literature
/-- DISCLOSED standard external input, not a paper-specific axiom.  See the
accompanying STANDARD_INPUTS.md for the Chern--Weil/dd^c/psh scope. -/
axiom independent_current_psh_metric_reconstruction :
  IndependentCurrentMetricBridge.ReconstructionStatement
end FailureOfSemipositiveMetricExtension.Literature

namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.FreshCurrentBridge
noncomputable section
open Set MeasureTheory IsManifold
open scoped ContDiff
open WeakComplexHessian PshCurvatureCurrentInterface DistributionalCurrent
open NegativeCurveAdapter IndependentCurrentMetricBridge

abbrev actualCoordinateAtlas : CoordinateAtlas (Fiber 0) CurrentIndex :=
  metricCoordinateAtlas centralMetricAtlas

def actualFrameAtlas : FrameAtlas (A := CurrentIndex) (line (-2) (fun _ => 1)) where
  coordinates := actualCoordinateAtlas
  frame := Prod.fst
  source_frame a := fun _ h => h.2
  frame_cover i p hp := by
    obtain ⟨⟨r,e⟩,hr⟩ := FixedFiber.charts_cover 0 p
    exact ⟨(i,r,e),rfl,hr,hp⟩

def actualReferenceCurrent : PositiveCurrent actualCoordinateAtlas :=
  metricCurrent centralH0_globalCoordinateCurrent

theorem actual_reference_represents :
    Represents actualFrameAtlas actualReferenceCurrent (weight centralH0) where
  finite_ae a := (centralH0_globalCoordinateCurrent.localCurrent a).finite_ae
  coefficient_eq _ _ _ _ _ := rfl

/-- Curvature presentation of the real c1 of the SAME actual L.  This is not
an integral/singular-cohomology implementation. -/
def actualRealChernClass : DeRhamCurrentClass actualCoordinateAtlas :=
  deRhamClass actualReferenceCurrent.toCurrent

/-- The original independent T, not a selected metric's current. -/
theorem actual_current_same_metric
    (T : PositiveCurrent actualCoordinateAtlas)
    (hc : deRhamClass T.toCurrent = actualRealChernClass) :
    ∃ h : SingularHermitianWeight 0 (-2) (fun _ => 1),
      HasPlurisubharmonicWeights h ∧ Represents actualFrameAtlas T (weight h) := by
  obtain ⟨h,hh,hrep⟩ := Literature.independent_current_psh_metric_reconstruction
    (Fiber 0) CurrentIndex Index (Fin 4 × Fin 2) CaoAdapter.centralAtlas
      immersion (line (-2) (fun _ => 1)) actualFrameAtlas (weight centralH0)
      (weight_psh centralH0 centralH0_plurisubharmonic)
      actualReferenceCurrent T actual_reference_represents hc
  let h' : SingularHermitianWeight 0 (-2) (fun _ => 1) := ⟨h.weight,h.compatible⟩
  refine ⟨h',?_,hrep⟩
  intro i r e
  exact hh (r,e) i

/-- Retain positivity of the SAME residual witness instead of forgetting it. -/
structure RetainedResidual (h : SingularHermitianWeight 0 (-2) (fun _ => 1))
    extends HalfDivisorResidual h where
  psh : HasPlurisubharmonicWeights remainder

theorem retained_residual_exists (h : SingularHermitianWeight 0 (-2) (fun _ => 1))
    (hh : HasPlurisubharmonicWeights h) : Nonempty (RetainedResidual h) := by
  obtain ⟨r⟩ := Literature.negative_curve_psh_removal_via_zariski_siu_translation
    CaoAdapter.centralAtlas (line (-2) (fun _ => 1)) (line (-2) centralADegree)
      (line (-2) ellDegree) immersion 2 2 (by norm_num) (by norm_num)
      powerProduct generators divisor a_hasPullbackDegree ell_hasPullbackDegree
      (weight h) (weight_psh h hh)
  refine ⟨{ toHalfDivisorResidual := halfDivisorResidual h r, psh := ?_ }⟩
  intro i a b
  exact r.psh (a,b) i

/-- A bounded, same-witness adapter: quantification over independent T is
preserved through reconstruction, residual positivity and minimal comparison. -/
theorem actual_current_same_metric_and_residual
    (T : PositiveCurrent actualCoordinateAtlas)
    (hc : deRhamClass T.toCurrent = actualRealChernClass) :
    ∃ h : SingularHermitianWeight 0 (-2) (fun _ => 1),
      HasPlurisubharmonicWeights h ∧ Represents actualFrameAtlas T (weight h) ∧
      ∃ r : RetainedResidual h, ∃ C : ℝ, ∀ i p, p ∈ baseSet 0 i →
        h.weight i p ≤ centralH0.weight i p + (C : WithBot ℝ) := by
  obtain ⟨h,hh,hrep⟩ := actual_current_same_metric T hc
  obtain ⟨r⟩ := retained_residual_exists h hh
  exact ⟨h,hh,hrep,r,central_weight_le_h0_of_residual h r.toHalfDivisorResidual⟩
end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.FreshCurrentBridge
