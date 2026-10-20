import FailureOfSemipositiveMetricExtension.GeneralMultiplierGerms
import FailureOfSemipositiveMetricExtension.CaoExtensionInterface
import Mathlib.Topology.Algebra.Module.Alternating.Basic

/-! A genuine smooth closed positive J-invariant real two-form on an arbitrary
finite-dimensional complex manifold. It is explicit differential-form data,
not a projective-immersion substitute for the Kähler hypothesis. -/
namespace FailureOfSemipositiveMetricExtension.GeneralKahler
noncomputable section
open Set IsManifold
open scoped Manifold ContDiff

abbrev Coord (n : ℕ) := Fin n → ℂ
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coord n) M]

abbrev TwoForm := ∀ p : M, (TangentSpace 𝓘(ℂ,Coord n) p) [⋀^Fin 2]→L[ℝ] ℝ

/-- Evaluate the actual pullback two-form on constant coordinate vectors. -/
def coordinateCoefficient (η : TwoForm (n := n) (M := M))
    (e : PartialHomeomorph M (Coord n)) (v w z : Coord n) : ℝ :=
  η (e.symm z) ![mfderiv 𝓘(ℂ,Coord n) 𝓘(ℂ,Coord n) e.symm z v,
    mfderiv 𝓘(ℂ,Coord n) 𝓘(ℂ,Coord n) e.symm z w]

/-- Kähler form data with real smoothness in the actual analytic atlas. The
cyclic derivative identity is exactly dω=0 in local coordinates. -/
structure KahlerForm {A : Type}
    (atlas : CaoExtensionInterface.AnalyticAtlas (Coord n) M A) where
  form : TwoForm (n := n) (M := M)
  smooth : ∀ (a : A) (v w : Coord n),
    ContDiffOn ℝ ∞ (coordinateCoefficient form (atlas.chart a) v w) (atlas.chart a).target
  closed : ∀ (a : A) (z : Coord n), z ∈ (atlas.chart a).target → ∀ v w q : Coord n,
    fderiv ℝ (coordinateCoefficient form (atlas.chart a) w q) z v +
      fderiv ℝ (coordinateCoefficient form (atlas.chart a) q v) z w +
        fderiv ℝ (coordinateCoefficient form (atlas.chart a) v w) z q = 0
  J_invariant : ∀ (p : M) (v w : TangentSpace 𝓘(ℂ,Coord n) p),
    form p ![Complex.I • v,Complex.I • w] = form p ![v,w]
  positive : ∀ (p : M) (v : TangentSpace 𝓘(ℂ,Coord n) p), v ≠ 0 →
    0 < form p ![v,Complex.I • v]

/-- Nondegeneracy is a proved consequence, rather than an extra unverified field. -/
theorem KahlerForm.nondegenerate {A : Type}
    {atlas : CaoExtensionInterface.AnalyticAtlas (Coord n) M A} (η : KahlerForm atlas)
    (p : M) {v : TangentSpace 𝓘(ℂ,Coord n) p}
    (hv : ∀ w, η.form p ![v,w] = 0) : v = 0 := by
  by_contra h
  have hp := η.positive p v h
  rw [hv (Complex.I • v)] at hp
  exact lt_irrefl 0 hp

end
end FailureOfSemipositiveMetricExtension.GeneralKahler
