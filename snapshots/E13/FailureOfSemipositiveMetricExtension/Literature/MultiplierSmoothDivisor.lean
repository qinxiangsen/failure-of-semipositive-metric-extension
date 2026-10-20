import FailureOfSemipositiveMetricExtension.MultiplierGerms
import Mathlib.Algebra.Order.Floor.Semiring

/-! EXTERNAL LITERATURE THEOREM: local multiplier-ideal formula for a smooth divisor.
Demailly, Analytic Methods in Algebraic Geometry, Remark 5.9, printed p.38;
Definition 5.1 and the locally bounded factor convention of multiplier ideals.
The statement below is the one-component SNC formula in actual holomorphic local
rings, with actual nonnegative Lebesgue integrals. It applies to arbitrary complex
surfaces, equations, weights and exponents; no object of the uploaded paper occurs.
This is a proposed next-stage interface, not imported by the frozen stage-4 root. -/
namespace FailureOfSemipositiveMetricExtension.Literature
open Set TopologicalSpace
open scoped Manifold ContDiff

axiom smooth_divisor_multiplier_germ
    (M : Type) [TopologicalSpace M] [ChartedSpace FailureOfSemipositiveMetricExtension.Multiplier.Coord M]
    [IsManifold 𝓘(ℂ,FailureOfSemipositiveMetricExtension.Multiplier.Coord) ω M]
    (U : Opens M)
    (d : C^∞⟮𝓘(ℂ,FailureOfSemipositiveMetricExtension.Multiplier.Coord),U;𝓘(ℂ),ℂ⟯)
    (p : M) (hp : p ∈ U)
    (ψ : M → ℝ) (hψ : ContinuousOn ψ U)
    (c : ℝ) (hc : 0 ≤ c) (w : M → WithBot ℝ)
    (hw : ∀ x ∈ U, w x =
      if FailureOfSemipositiveMetricExtension.Multiplier.sectionFunction M U d x = 0 then ⊥ else
        ((ψ x + c * Real.log (Complex.normSq (FailureOfSemipositiveMetricExtension.Multiplier.sectionFunction M U d x)) : ℝ) : WithBot ℝ))
    (hsimple : d ⟨p,hp⟩ = 0 → FailureOfSemipositiveMetricExtension.Multiplier.SimpleEquationAt M U d p)
    (m : ℕ) (g : FailureOfSemipositiveMetricExtension.Multiplier.Stalk M p) :
    FailureOfSemipositiveMetricExtension.Multiplier.IntegrableGerm M m w p g ↔
      g ∈ Ideal.span {((FailureOfSemipositiveMetricExtension.Multiplier.sheaf M).presheaf.germ U p hp d) ^
        Nat.floor ((m:ℝ) * c)}

end FailureOfSemipositiveMetricExtension.Literature
