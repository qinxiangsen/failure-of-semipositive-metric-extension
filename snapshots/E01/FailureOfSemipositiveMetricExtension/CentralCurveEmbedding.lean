import FailureOfSemipositiveMetricExtension.CentralCurveManifold
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-! The actual central rational curve is analytically embedded, not merely
homeomorphic to a projective line: its tangent inclusion has a verified
continuous complex-linear left inverse at every point. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

/-- The fourth direction gives an actual global analytic retraction onto ℓ. -/
def curveRetraction (p : Fiber 0) : EllCurve := lineCurveParam (FixedFiber.direction 0 3 p)

@[simp] theorem curveRetraction_inclusion (p : EllCurve) : curveRetraction p.val = p :=
  lineCurveParam_inverse p

theorem curveRetraction_contMDiff (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) n curveRetraction :=
  (lineCurveParam_contMDiff n).comp (FixedFiber.direction_contMDiff 0 3 n)

theorem curveInclusion_isClosedEmbedding : IsClosedEmbedding (fun p : EllCurve => p.val) :=
  ellZeroSet_isClosed.isClosedEmbedding_subtypeVal

/-- An actual left inverse to the complex manifold derivative of the inclusion. -/
theorem curveInclusion_mfderiv_leftInverse (p : EllCurve) :
    ∃ L : TangentSpace 𝓘(ℂ,FixedFiber.Coord) p.val →L[ℂ] TangentSpace 𝓘(ℂ) p,
      L.comp (mfderiv 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) (fun q : EllCurve => q.val) p) =
        ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ) p) := by
  refine ⟨mfderiv 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) curveRetraction p.val,?_⟩
  have hid : curveRetraction ∘ (fun q : EllCurve => q.val) = id := funext curveRetraction_inclusion
  apply ContinuousLinearMap.ext
  intro v
  have hc := mfderiv_comp_apply p
    (((curveRetraction_contMDiff 1) p.val).mdifferentiableAt le_rfl)
    (((curveInclusion_contMDiff 1) p).mdifferentiableAt le_rfl) v
  rw [hid,mfderiv_id] at hc
  exact hc.symm

theorem curveInclusion_mfderiv_injective (p : EllCurve) :
    Function.Injective (mfderiv 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) (fun q : EllCurve => q.val) p) := by
  obtain ⟨L,hL⟩ := curveInclusion_mfderiv_leftInverse p
  have hleft : Function.LeftInverse L
      (mfderiv 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) (fun q : EllCurve => q.val) p) :=
    fun v => congrArg (fun T => T v) hL
  exact hleft.injective

theorem ellCurve_tangent_finrank (p : EllCurve) : Module.finrank ℂ (TangentSpace 𝓘(ℂ) p) = 1 :=
  Module.finrank_self ℂ

/-- A genuine projective-line homeomorphism analytic in both directions. -/
theorem ellCurve_biholomorphic : ∃ e : Direction ≃ₜ EllCurve,
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω e ∧ ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω e.symm :=
  ⟨lineCurveHomeomorph,lineCurveParam_contMDiff ω,lineCurveInverse_contMDiff ω⟩

/-- All claimed compactness, analyticity, and embedding properties refer to the original zero locus. -/
theorem ellCurve_compact_analytic_embedded :
    CompactSpace EllCurve ∧ IsManifold 𝓘(ℂ) ω EllCurve ∧
      IsClosedEmbedding (fun p : EllCurve => p.val) ∧
      ContMDiff 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) ω (fun p : EllCurve => p.val) ∧
      ∀ p : EllCurve, Function.Injective
        (mfderiv 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) (fun q : EllCurve => q.val) p) :=
  ⟨inferInstance,inferInstance,curveInclusion_isClosedEmbedding,curveInclusion_contMDiff ω,
    curveInclusion_mfderiv_injective⟩

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
