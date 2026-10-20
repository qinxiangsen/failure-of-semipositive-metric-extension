import FailureOfSemipositiveMetricExtension.HisamotoManifold
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Normed.Group.Quotient

/-! The normal fibre of a ruling curve is the actual tangent-space quotient,
not a scalar surrogate. Differentiating the actual ruling coordinate gives a
global continuous linear trivialization of these quotient fibres. -/
namespace FailureOfSemipositiveMetricExtension.Hisamoto.RulingNormal
noncomputable section
open Set Topology
open scoped Manifold ContDiff

variable (i : Fin 2) (t : ℂ)

def fibreMap (p : Direction) : Point := localParam i (p,t)
def transverseMap (p : Direction) (z : ℂ) : Point := localParam i (p,z)
def retract (q : Point) : Direction := fiberDirection i (blowdown q)
def baseCoordinate (q : Point) : ℂ := ProjectiveLine.coordinates i (ruling q)

@[simp] theorem retract_fibreMap (p : Direction) : retract i (fibreMap i t p) = p := by
  simp [retract,fibreMap]
@[simp] theorem baseCoordinate_fibreMap (p : Direction) : baseCoordinate i (fibreMap i t p) = t := by
  simp [baseCoordinate,fibreMap]
@[simp] theorem baseCoordinate_transverseMap (p : Direction) (z : ℂ) :
    baseCoordinate i (transverseMap i p z) = z := by simp [baseCoordinate,transverseMap]

@[simp] theorem fibreMap_mem_rulingChart (p : Direction) : fibreMap i t p ∈ rulingChart i := by
  rw [rulingChart_eq_range]
  exact ⟨(p,t),rfl⟩

theorem fibreMap_contMDiff (n : WithTop ℕ∞) : ContMDiff 𝓘(ℂ) 𝓘(ℂ,Coord) n (fibreMap i t) :=
  (localParam_contMDiff i n).comp (contMDiff_id.prodMk contMDiff_const)

theorem transverseMap_contMDiff (p : Direction) (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ,Coord) n (transverseMap i p) :=
  (localParam_contMDiff i n).comp (contMDiff_const.prodMk contMDiff_id)

theorem retract_contMDiffAt (p : Direction) (n : WithTop ℕ∞) :
    ContMDiffAt 𝓘(ℂ,Coord) 𝓘(ℂ) n (retract i) (fibreMap i t p) :=
  ((localCoordinates_contMDiffOn i n).contMDiffAt
    ((rulingChart_isOpen i).mem_nhds (fibreMap_mem_rulingChart i t p))).fst

theorem baseCoordinate_contMDiffAt (p : Direction) (n : WithTop ℕ∞) :
    ContMDiffAt 𝓘(ℂ,Coord) 𝓘(ℂ) n (baseCoordinate i) (fibreMap i t p) :=
  ((localCoordinates_contMDiffOn i n).contMDiffAt
    ((rulingChart_isOpen i).mem_nhds (fibreMap_mem_rulingChart i t p))).snd

abbrev AmbientTangent (p : Direction) := TangentSpace 𝓘(ℂ,Coord) (fibreMap i t p)

def tangentMap (p : Direction) : TangentSpace 𝓘(ℂ) p →L[ℂ] AmbientTangent i t p :=
  mfderiv 𝓘(ℂ) 𝓘(ℂ,Coord) (fibreMap i t) p

def tangentImage (p : Direction) : Submodule ℂ (AmbientTangent i t p) :=
  LinearMap.range (tangentMap i t p).toLinearMap

abbrev NormalFiber (p : Direction) := AmbientTangent i t p ⧸ tangentImage i t p

def normalDerivative (p : Direction) : AmbientTangent i t p →L[ℂ] ℂ :=
  mfderiv 𝓘(ℂ,Coord) 𝓘(ℂ) (baseCoordinate i) (fibreMap i t p)

theorem retractDerivative_tangentMap (p : Direction) (v : TangentSpace 𝓘(ℂ) p) :
    mfderiv 𝓘(ℂ,Coord) 𝓘(ℂ) (retract i) (fibreMap i t p) (tangentMap i t p v) = v := by
  have h := mfderiv_comp_apply p ((retract_contMDiffAt i t p 1).mdifferentiableAt le_rfl)
    ((fibreMap_contMDiff i t 1 p).mdifferentiableAt le_rfl) v
  have he : retract i ∘ fibreMap i t = id := funext (retract_fibreMap i t)
  rw [he,mfderiv_id] at h
  exact h.symm

theorem tangentMap_injective (p : Direction) : Function.Injective (tangentMap i t p) := by
  intro v w h
  have he := congrArg (mfderiv 𝓘(ℂ,Coord) 𝓘(ℂ) (retract i) (fibreMap i t p)) h
  simpa only [retractDerivative_tangentMap] using he

theorem normalDerivative_tangentMap (p : Direction) (v : TangentSpace 𝓘(ℂ) p) :
    normalDerivative i t p (tangentMap i t p v) = 0 := by
  have h := mfderiv_comp_apply p ((baseCoordinate_contMDiffAt i t p 1).mdifferentiableAt le_rfl)
    ((fibreMap_contMDiff i t 1 p).mdifferentiableAt le_rfl) v
  have he : baseCoordinate i ∘ fibreMap i t = fun _ => t := funext (baseCoordinate_fibreMap i t)
  rw [he,mfderiv_const] at h
  exact h.symm

theorem normalDerivative_surjective (p : Direction) : Function.Surjective (normalDerivative i t p) := by
  intro v
  refine ⟨mfderiv 𝓘(ℂ) 𝓘(ℂ,Coord) (transverseMap i p) t v,?_⟩
  have h := mfderiv_comp_apply t ((baseCoordinate_contMDiffAt i t p 1).mdifferentiableAt le_rfl)
    ((transverseMap_contMDiff i p 1 t).mdifferentiableAt le_rfl) v
  have he : baseCoordinate i ∘ transverseMap i p = id := funext (baseCoordinate_transverseMap i p)
  rw [he,mfderiv_id] at h
  exact h.symm

instance ambientFiniteDimensional (p : Direction) : FiniteDimensional ℂ (AmbientTangent i t p) :=
  inferInstanceAs (FiniteDimensional ℂ (ℂ × ℂ))

theorem tangentImage_finrank (p : Direction) : Module.finrank ℂ (tangentImage i t p) = 1 := by
  rw [tangentImage,LinearMap.finrank_range_of_inj (tangentMap_injective i t p)]
  exact Module.finrank_self ℂ

theorem ambientTangent_finrank (p : Direction) : Module.finrank ℂ (AmbientTangent i t p) = 2 := by
  change Module.finrank ℂ (ℂ × ℂ) = 2
  simp

/-- Kernel equality for actual manifold differentials, with no normal-bundle hypothesis. -/
theorem tangentImage_eq_ker (p : Direction) :
    tangentImage i t p = LinearMap.ker (normalDerivative i t p).toLinearMap := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro v ⟨w,rfl⟩
    exact normalDerivative_tangentMap i t p w
  · have hdim := (normalDerivative i t p).toLinearMap.finrank_range_add_finrank_ker
    have hrange : LinearMap.range (normalDerivative i t p).toLinearMap = ⊤ :=
      LinearMap.range_eq_top.mpr (normalDerivative_surjective i t p)
    rw [hrange,finrank_top,Module.finrank_self,ambientTangent_finrank] at hdim
    rw [tangentImage_finrank]
    omega

/-- A genuine quotient-linear isomorphism, induced by the actual ruling differential. -/
def normalEquiv (p : Direction) : NormalFiber i t p ≃ₗ[ℂ] ℂ :=
  (Submodule.quotEquivOfEq _ _ (tangentImage_eq_ker i t p)).trans
    ((normalDerivative i t p).toLinearMap.quotKerEquivOfSurjective (normalDerivative_surjective i t p))

@[simp] theorem normalEquiv_mk (p : Direction) (v : AmbientTangent i t p) :
    normalEquiv i t p (Submodule.Quotient.mk v) = normalDerivative i t p v := rfl

instance tangentImage_isClosed (p : Direction) : IsClosed (tangentImage i t p : Set (AmbientTangent i t p)) :=
  (tangentImage i t p).closed_of_finiteDimensional

/-- Continuous for the standard closed-subspace quotient topology. -/
def normalContinuousEquiv (p : Direction) : NormalFiber i t p ≃L[ℂ] ℂ :=
  (normalEquiv i t p).toContinuousLinearEquiv

end
end FailureOfSemipositiveMetricExtension.Hisamoto.RulingNormal
