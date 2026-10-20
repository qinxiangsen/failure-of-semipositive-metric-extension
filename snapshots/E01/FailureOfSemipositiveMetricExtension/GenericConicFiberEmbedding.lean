import FailureOfSemipositiveMetricExtension.GenericConicFiberManifold
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-! The complete generic pencil fibre is a genuinely embedded compact analytic
projective line. Its tangent inclusion has an explicit analytic left inverse. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil.Conic
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

def fiberRetraction (c : Data) (p : Fiber c.t) : PencilFiber c :=
  fiberParam c (FixedFiber.direction c.t 3 p)

@[simp] theorem fiberRetraction_inclusion (c : Data) (p : PencilFiber c) :
    fiberRetraction c p.val = p := fiberParam_inverse c p

theorem fiberRetraction_contMDiff (c : Data) (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) n (fiberRetraction c) :=
  (fiberParam_contMDiff c n).comp (FixedFiber.direction_contMDiff c.t 3 n)

theorem fiberInclusion_isClosedEmbedding (c : Data) : IsClosedEmbedding (fun p : PencilFiber c => p.val) :=
  (pencilFiber_isClosed c).isClosedEmbedding_subtypeVal

/-- An actual left inverse to the complex manifold derivative of the inclusion. -/
theorem fiberInclusion_mfderiv_leftInverse (c : Data) (p : PencilFiber c) :
    ∃ L : TangentSpace 𝓘(ℂ,FixedFiber.Coord) p.val →L[ℂ] TangentSpace 𝓘(ℂ) p,
      L.comp (mfderiv 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) (fun q : PencilFiber c => q.val) p) =
        ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ) p) := by
  refine ⟨mfderiv 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) (fiberRetraction c) p.val,?_⟩
  have hid : fiberRetraction c ∘ (fun q : PencilFiber c => q.val) = id := funext (fiberRetraction_inclusion c)
  apply ContinuousLinearMap.ext
  intro v
  have hc := mfderiv_comp_apply p
    (((fiberRetraction_contMDiff c 1) p.val).mdifferentiableAt le_rfl)
    (((fiberInclusion_contMDiff c 1) p).mdifferentiableAt le_rfl) v
  rw [hid,mfderiv_id] at hc
  exact hc.symm

theorem fiberInclusion_mfderiv_injective (c : Data) (p : PencilFiber c) :
    Function.Injective (mfderiv 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) (fun q : PencilFiber c => q.val) p) := by
  obtain ⟨L,hL⟩ := fiberInclusion_mfderiv_leftInverse c p
  have hleft : Function.LeftInverse L
      (mfderiv 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) (fun q : PencilFiber c => q.val) p) :=
    fun v => congrArg (fun T => T v) hL
  exact hleft.injective

theorem pencilFiber_biholomorphic (c : Data) : ∃ e : Direction ≃ₜ PencilFiber c,
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω e ∧ ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω e.symm :=
  ⟨fiberHomeomorph c,fiberParam_contMDiff c ω,fiberInverse_contMDiff c ω⟩

/-- All properties refer to the entire actual pencil fibre and its original
subtype topology, rather than to an assumed abstract replacement curve. -/
theorem pencilFiber_compact_analytic_embedded (c : Data) :
    CompactSpace (PencilFiber c) ∧ IsManifold 𝓘(ℂ) ω (PencilFiber c) ∧
      IsClosedEmbedding (fun p : PencilFiber c => p.val) ∧
      ContMDiff 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) ω (fun p : PencilFiber c => p.val) ∧
      ∀ p : PencilFiber c, Function.Injective
        (mfderiv 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) (fun q : PencilFiber c => q.val) p) :=
  ⟨inferInstance,inferInstance,fiberInclusion_isClosedEmbedding c,fiberInclusion_contMDiff c ω,
    fiberInclusion_mfderiv_injective c⟩

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil.Conic
