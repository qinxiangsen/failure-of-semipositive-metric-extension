import FailureOfSemipositiveMetricExtension.CentralCurvePullbackIsomorphism

/-! The actual line, divisor, and generated cubic bundle have standard analytic
pullbacks O(-1), O(-2), and O(0), respectively. These are genuine bundle
homeomorphisms with analytic inverse and complex-linear fibre maps, rather than
an appeal to numerical degree or intersection theory. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.CurvePullback
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

/-- The actual L₀ restricted to the actual projective line. -/
def lHomeomorph : PullbackTotal (-2) (fun _ => 1) ≃ₜ (ProjectiveLineBundle.core (-1)).TotalSpace :=
  degreeHomeomorph (-2) (fun _ => 1)

/-- The actual divisor bundle of ℓ restricted to ℓ. -/
def ellHomeomorph : PullbackTotal (-2) ellDegree ≃ₜ (ProjectiveLineBundle.core (-2)).TotalSpace :=
  degreeHomeomorph (-2) ellDegree

/-- The actual generated cubic bundle A restricted to ℓ. -/
def aHomeomorph : PullbackTotal (-2) centralADegree ≃ₜ (ProjectiveLineBundle.core 0).TotalSpace :=
  degreeHomeomorph (-2) centralADegree

theorem lHomeomorph_analytic :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω lHomeomorph ∧
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω lHomeomorph.symm :=
  ⟨degreeHomeomorph_contMDiff (-2) (fun _ => 1),degreeHomeomorph_symm_contMDiff (-2) (fun _ => 1)⟩

theorem ellHomeomorph_analytic :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω ellHomeomorph ∧
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω ellHomeomorph.symm :=
  ⟨degreeHomeomorph_contMDiff (-2) ellDegree,degreeHomeomorph_symm_contMDiff (-2) ellDegree⟩

theorem aHomeomorph_analytic :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω aHomeomorph ∧
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω aHomeomorph.symm :=
  ⟨degreeHomeomorph_contMDiff (-2) centralADegree,degreeHomeomorph_symm_contMDiff (-2) centralADegree⟩

def lFiberEquiv (d : Direction) :
    PullbackFiber (-2) (fun _ => 1) d ≃L[ℂ] (ProjectiveLineBundle.core (-1)).Fiber d :=
  degreeFiberEquiv (-2) (fun _ => 1) d

def ellFiberEquiv (d : Direction) :
    PullbackFiber (-2) ellDegree d ≃L[ℂ] (ProjectiveLineBundle.core (-2)).Fiber d :=
  degreeFiberEquiv (-2) ellDegree d

def aFiberEquiv (d : Direction) :
    PullbackFiber (-2) centralADegree d ≃L[ℂ] (ProjectiveLineBundle.core 0).Fiber d :=
  degreeFiberEquiv (-2) centralADegree d

@[simp] theorem lHomeomorph_mk (d : Direction) (v : PullbackFiber (-2) (fun _ => 1) d) :
    lHomeomorph ⟨d,v⟩ = ⟨d,lFiberEquiv d v⟩ := rfl
@[simp] theorem ellHomeomorph_mk (d : Direction) (v : PullbackFiber (-2) ellDegree d) :
    ellHomeomorph ⟨d,v⟩ = ⟨d,ellFiberEquiv d v⟩ := rfl
@[simp] theorem aHomeomorph_mk (d : Direction) (v : PullbackFiber (-2) centralADegree d) :
    aHomeomorph ⟨d,v⟩ = ⟨d,aFiberEquiv d v⟩ := rfl

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.CurvePullback

namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

/-- The parametrization from the actual standard P¹ has an actual derivative
left inverse, supplied by the fourth projective direction. -/
theorem lineParam_mfderiv_leftInverse (d : Direction) :
    ∃ L : TangentSpace 𝓘(ℂ,FixedFiber.Coord) (lineParam d) →L[ℂ] TangentSpace 𝓘(ℂ) d,
      L.comp (mfderiv 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) lineParam d) =
        ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ) d) := by
  refine ⟨mfderiv 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) (FixedFiber.direction 0 3) (lineParam d),?_⟩
  have hid : FixedFiber.direction 0 3 ∘ lineParam = id := funext lineParam_direction_three
  apply ContinuousLinearMap.ext
  intro v
  have hc := mfderiv_comp_apply d
    (((FixedFiber.direction_contMDiff 0 3 1) (lineParam d)).mdifferentiableAt le_rfl)
    (((lineParam_contMDiff 1) d).mdifferentiableAt le_rfl) v
  rw [hid,mfderiv_id] at hc
  exact hc.symm

theorem lineParam_mfderiv_injective (d : Direction) :
    Function.Injective (mfderiv 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) lineParam d) := by
  obtain ⟨L,hL⟩ := lineParam_mfderiv_leftInverse d
  exact (show Function.LeftInverse L (mfderiv 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) lineParam d) from
    fun v => congrArg (fun T => T v) hL).injective

/-- One explicit closed holomorphic immersion of the actual P¹ into the original
central surface, whose image is exactly the actual zero locus of ℓ. -/
theorem lineParam_closed_holomorphic_embedding :
    IsClosedEmbedding lineParam ∧
    ContMDiff 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) ω lineParam ∧
    ∀ d : Direction, Function.Injective (mfderiv 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) lineParam d) :=
  ⟨lineParam_isClosedEmbedding,lineParam_contMDiff ω,lineParam_mfderiv_injective⟩

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
