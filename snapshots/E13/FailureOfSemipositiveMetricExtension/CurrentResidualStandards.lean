import FailureOfSemipositiveMetricExtension.IndependentCurrentMetricBridge
import FailureOfSemipositiveMetricExtension.DistributionalCurrentAlgebra
import FailureOfSemipositiveMetricExtension.PoincareLelongIntegrationInterface

/-! Explicit, universal standard distribution-current interfaces.  These
statements mention no special surface, bundle, ell, exponent 2, or h0.  Their
inputs are test-coefficient identities and literal local weight identities. -/
namespace FailureOfSemipositiveMetricExtension.CurrentResidualStandards
noncomputable section
open Set MeasureTheory Filter IsManifold
open scoped Manifold ContDiff Topology
open WeakComplexHessian PshCurvatureCurrentInterface DistributionalCurrent
abbrev Coord := ℂ × ℂ
variable {M A : Type} [TopologicalSpace M] [ChartedSpace Coord M]

def HasTraceLelongNumber {D : CoordinateAtlas M A} (T : PositiveCurrent D)
    (a : A) (z : Coord) (v : ℝ) : Prop :=
  Tendsto (fun r : ℝ => (T.traceMeasure a (euclideanBall z r)).toReal /
    (Real.pi * r^2)) (𝓝[>] 0) (𝓝 v)

def LocallyIntegrableGlobal (D : CoordinateAtlas M A) (u : M → WithBot ℝ) : Prop :=
  ∀ a, LocallyIntegrableOn (realRepresentative
    (fun z => u ((D.coordinate a).chart.symm z))) (D.coordinate a).chart.target

/-- Local dd^c linearity, psh regularity, and global dd^c-exactness.  It does
not assert existence of the global potential: the caller supplies ONE u and
proves its exact local relation to the SAME residual r. -/
def ResidualCalculusStatement : Prop :=
  ∀ (M A : Type) [TopologicalSpace M] [ChartedSpace Coord M]
    [T2Space M] [SecondCountableTopology M] [IsManifold 𝓘(ℂ,Coord) ω M],
    ∀ (D : CoordinateAtlas M A) (T I : PositiveCurrent D) (S : Current D)
      (h r w : A → Coord → WithBot ℝ) (g : A → Coord → ℝ)
      (u : M → WithBot ℝ) (m : ℝ), 0 < m →
      (∀ a, PlurisubharmonicOn (h a) (D.coordinate a).chart.target) →
      (∀ a, PlurisubharmonicOn (r a) (D.coordinate a).chart.target) →
      (∀ a, ∀ᵐ z ∂volume.restrict (D.coordinate a).chart.target, h a z ≠ ⊥) →
      (∀ a, ∀ᵐ z ∂volume.restrict (D.coordinate a).chart.target, r a z ≠ ⊥) →
      (∀ a, LocallyIntegrableOn (realRepresentative (w a)) (D.coordinate a).chart.target) →
      (∀ a, ∀ᵐ z ∂volume.restrict (D.coordinate a).chart.target, w a z ≠ ⊥) →
      (∀ a, ContDiffOn ℝ ω (g a) (D.coordinate a).chart.target) →
      (∀ a f, IsTest (D.coordinate a).chart.target f → ∀ j k,
        coefficient (realRepresentative (h a)) j k f = T.coefficient a j k f) →
      (∀ a f, IsTest (D.coordinate a).chart.target f → ∀ j k,
        coefficient (realRepresentative (w a)) j k f = I.coefficient a j k f) →
      (∀ a f, IsTest (D.coordinate a).chart.target f → ∀ j k,
        coefficient (g a) j k f = S.coefficient a j k f) →
      (∀ a z, z ∈ (D.coordinate a).chart.target →
        scaleWeight m (h a z) = r a z + w a z) →
      (∀ a z, z ∈ (D.coordinate a).chart.target →
        scaleWeight m⁻¹ (r a z) = u ((D.coordinate a).chart.symm z) +
          ((m⁻¹ * g a z : ℝ) : WithBot ℝ)) →
      (T.toCurrent.add (I.toCurrent.smul (-m⁻¹))).IsPositive ∧
      LocallyIntegrableGlobal D u ∧
      deRhamClass (T.toCurrent.add (I.toCurrent.smul (-m⁻¹))) =
        deRhamClass (S.smul m⁻¹) ∧
      ∀ a f, IsTest (D.coordinate a).chart.target f → ∀ j k,
        T.coefficient a j k f - (m⁻¹ : ℂ) * I.coefficient a j k f =
          (m⁻¹ : ℂ) * S.coefficient a j k f +
          coefficient (realRepresentative (fun z => u ((D.coordinate a).chart.symm z))) j k f

/-- Normalization of integration over a reduced smooth complex curve: its
actual Euclidean area trace has mass-Lelong number one, in every chart. -/
def DivisorNormalizationStatement : Prop :=
  ∀ (M A J : Type) [TopologicalSpace M] [ChartedSpace Coord M]
    [T2Space M] [SecondCountableTopology M] [IsManifold 𝓘(ℂ,Coord) ω M],
    ∀ (D : CoordinateAtlas M A) (L : NegativeCurveRemovalInterface.AnalyticLine M J)
      (s : NegativeCurveRemovalInterface.RationalSimpleDivisor L) (I : PositiveCurrent D),
      (∀ a, I.traceMeasure a = PoincareLelongIntegrationInterface.integrationTraceMeasure
        (PoincareLelongIntegrationInterface.curveInChart D L s a)
        (PoincareLelongIntegrationInterface.curveParameterDomain D L s a)) →
      ∀ p, p ∈ Set.range s.curve → ∀ a, p ∈ (D.coordinate a).chart.source →
        HasTraceLelongNumber I a ((D.coordinate a).chart p) 1

/-- Siu/Lelong monotonicity for arbitrary independent positive currents.
The positive residual is an INPUT here, not the desired paper theorem. -/
def LelongMonotonicityStatement : Prop :=
  ∀ (M A : Type) [TopologicalSpace M] [ChartedSpace Coord M]
    [T2Space M] [SecondCountableTopology M] [IsManifold 𝓘(ℂ,Coord) ω M],
    ∀ (D : CoordinateAtlas M A) (T I : PositiveCurrent D) (c : ℝ), 0 ≤ c →
      (T.toCurrent.add (I.toCurrent.smul (-c))).IsPositive →
      ∀ a z, z ∈ (D.coordinate a).chart.target → HasTraceLelongNumber I a z 1 →
        ∃ v : ℝ, HasTraceLelongNumber T a z v ∧ c ≤ v
end
end FailureOfSemipositiveMetricExtension.CurrentResidualStandards

namespace FailureOfSemipositiveMetricExtension.Literature
axiom residual_current_local_calculus : CurrentResidualStandards.ResidualCalculusStatement
axiom reduced_curve_integration_lelong_one : CurrentResidualStandards.DivisorNormalizationStatement
axiom positive_current_lelong_monotonicity : CurrentResidualStandards.LelongMonotonicityStatement
end FailureOfSemipositiveMetricExtension.Literature
