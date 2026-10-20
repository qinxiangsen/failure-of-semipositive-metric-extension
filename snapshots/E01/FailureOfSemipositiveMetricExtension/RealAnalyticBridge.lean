import FailureOfSemipositiveMetricExtension.GlobalFiberManifold
import Mathlib.Geometry.Manifold.Algebra.Monoid

/-! Restriction of complex analytic regularity to the underlying real manifolds. -/
namespace FailureOfSemipositiveMetricExtension
noncomputable section
open Set IsManifold
open scoped Manifold ContDiff

theorem complex_contMDiffWithinAt_real {E F M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace M] [ChartedSpace E M]
    {n : WithTop ℕ∞} {f : M → F} {s : Set M} {p : M}
    (h : ContMDiffWithinAt 𝓘(ℂ,E) 𝓘(ℂ,F) n f s p) :
    ContMDiffWithinAt 𝓘(ℝ,E) 𝓘(ℝ,F) n f s p := by
  rw [contMDiffWithinAt_iff] at h ⊢
  exact ⟨h.1,h.2.restrict_scalars ℝ⟩

theorem complex_contMDiffOn_real {E F M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace M] [ChartedSpace E M]
    {n : WithTop ℕ∞} {f : M → F} {s : Set M}
    (h : ContMDiffOn 𝓘(ℂ,E) 𝓘(ℂ,F) n f s) :
    ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,F) n f s := fun p hp => complex_contMDiffWithinAt_real (h p hp)

theorem complex_contMDiff_real {E F M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace M] [ChartedSpace E M]
    {n : WithTop ℕ∞} {f : M → F}
    (h : ContMDiff 𝓘(ℂ,E) 𝓘(ℂ,F) n f) :
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) n f := fun p => complex_contMDiffWithinAt_real (h p)

instance global_realIsManifold (n : WithTop ℕ∞) :
    IsManifold 𝓘(ℝ,GlobalIncidence.ChartCoord) n GlobalIncidence.Total := by
  apply isManifold_of_contDiffOn
  intro c c' hc hc'
  simpa using (GlobalIncidence.atlas_contDiffOn n c c' hc hc').restrict_scalars ℝ

instance fiber_realIsManifold (t : ℂ) (n : WithTop ℕ∞) :
    IsManifold 𝓘(ℝ,GlobalIncidence.FixedFiber.Coord) n (GlobalIncidence.Fiber t) := by
  apply isManifold_of_contDiffOn
  intro c c' hc hc'
  simpa using (GlobalIncidence.FixedFiber.atlas_contDiffOn t n c c' hc hc').restrict_scalars ℝ

theorem normSq_contDiff_real (n : WithTop ℕ∞) : ContDiff ℝ n Complex.normSq := by
  change ContDiff ℝ n (fun z : ℂ => z.re*z.re+z.im*z.im)
  exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
    (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
end
end FailureOfSemipositiveMetricExtension
