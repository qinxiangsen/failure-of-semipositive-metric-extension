import FailureOfSemipositiveMetricExtension.GlobalLocalSections
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-! The actual family projection is a complex analytic submersion. This is proved
from the explicit local analytic sections, not assumed as a family hypothesis. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence
noncomputable section
open Set IsManifold
open scoped Manifold ContDiff

/-- At every point the genuine manifold derivative has a continuous complex-linear right inverse. -/
theorem projection_mfderiv_rightInverse (p : Total) :
    ∃ R : TangentSpace 𝓘(ℂ) (projection p) →L[ℂ] TangentSpace 𝓘(ℂ,ChartCoord) p,
      (mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ) projection p).comp R =
        ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ) (projection p)) := by
  obtain ⟨s,hs,hsec,hreg⟩ := projection_local_analytic_section p 1
  refine ⟨mfderiv 𝓘(ℂ) 𝓘(ℂ,ChartCoord) s (projection p),?_⟩
  have hid : projection ∘ s = id := funext hsec
  apply ContinuousLinearMap.ext
  intro v
  have hc := mfderiv_comp_apply_of_eq (projection p)
    (((projection_contMDiff 1) p).mdifferentiableAt le_rfl)
    (hreg.mdifferentiableAt le_rfl) hs v
  rw [hid,mfderiv_id] at hc
  exact hc.symm

/-- Surjectivity concerns the actual manifold tangent map at every point. -/
theorem projection_mfderiv_surjective (p : Total) :
    Function.Surjective (mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ) projection p) := by
  obtain ⟨R,hR⟩ := projection_mfderiv_rightInverse p
  intro v
  exact ⟨R v,congrArg (fun T => T v) hR⟩

/-- All four substantive analytic family properties have been proved on the constructed space. -/
theorem proper_analytic_submersion :
    IsProperMap projection ∧ ContMDiff 𝓘(ℂ,ChartCoord) 𝓘(ℂ) ω projection ∧
    IsOpenMap projection ∧ ∀ p, Function.Surjective (mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ) projection p) :=
  ⟨projection_isProperMap,projection_contMDiff ω,projection_isOpenMap,projection_mfderiv_surjective⟩
end
end FailureOfSemipositiveMetricExtension.GlobalIncidence
