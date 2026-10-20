import FailureOfSemipositiveMetricExtension.GlobalAmbientAnalytic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-! The original incidence inclusion is an actual analytic closed immersion.
An explicit ambient analytic local retraction gives a continuous complex-linear
left inverse to its genuine manifold derivative at every point. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence
noncomputable section
open Set Topology IsManifold
open scoped Manifold ContDiff

/-- The ambient extension of the local threefold retraction. It is only asserted
to be analytic near points of its specified chart source. -/
def ambientRetraction (r : Fin 4) (e : Fin 2) : Ambient → Total :=
  chartParam r e ∘ ambientCoordinates r e

theorem ambientRetraction_inclusion (r : Fin 4) (e : Fin 2) (p : Total)
    (hp : p ∈ chartSource r e) : ambientRetraction r e p.val = p := by
  change chartParam r e (ambientCoordinates r e p.val) = p
  rw [ambientCoordinates_chartSource r e p hp]
  exact chartParam_coordinates r e p hp

theorem ambientRetraction_contMDiffAt (r : Fin 4) (e : Fin 2) (n : WithTop ℕ∞)
    (p : Total) (hp : p ∈ chartSource r e) :
    ContMDiffAt ambientModel 𝓘(ℂ,ChartCoord) n (ambientRetraction r e) p.val := by
  have hb := ((mem_chartSource_iff r e p).mp hp).1
  have hd := ((mem_chartSource_iff r e p).mp hp).2.1
  have hq : ambientCoordinates r e p.val ∈ chartDomain r e := by
    rw [ambientCoordinates_chartSource r e p hp]
    exact (homeomorphChart r e).map_source hp
  exact ((chartParam_contMDiffOn r e n).contMDiffAt
    ((chartDomain_isOpen r e).mem_nhds hq)).comp p.val
    (ambientCoordinates_contMDiffAt r e n p.val hb hd)

theorem ambientRetraction_inclusion_eventuallyEq (r : Fin 4) (e : Fin 2)
    (p : Total) (hp : p ∈ chartSource r e) :
    ambientRetraction r e ∘ (fun q : Total => q.val) =ᶠ[𝓝 p] id := by
  filter_upwards [(chartSource_isOpen r e).mem_nhds hp] with q hq
  exact ambientRetraction_inclusion r e q hq

/-- Each valid chart gives an actual complex-linear left inverse on tangent
spaces, computed from the derivative of its ambient local retraction. -/
theorem total_inclusion_mfderiv_chart_leftInverse (r : Fin 4) (e : Fin 2)
    (p : Total) (hp : p ∈ chartSource r e) :
    (mfderiv ambientModel 𝓘(ℂ,ChartCoord) (ambientRetraction r e) p.val).comp
      (mfderiv 𝓘(ℂ,ChartCoord) ambientModel (fun q : Total => q.val) p) =
        ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ,ChartCoord) p) := by
  have heq := (ambientRetraction_inclusion_eventuallyEq r e p hp).mfderiv_eq
    (I := 𝓘(ℂ,ChartCoord)) (I' := 𝓘(ℂ,ChartCoord))
  apply ContinuousLinearMap.ext
  intro v
  have hc := mfderiv_comp_apply p
    ((ambientRetraction_contMDiffAt r e 1 p hp).mdifferentiableAt le_rfl)
    (((total_inclusion_contMDiff 1) p).mdifferentiableAt le_rfl) v
  rw [heq,mfderiv_id] at hc
  exact hc.symm

theorem total_inclusion_mfderiv_leftInverse (p : Total) :
    ∃ L : TangentSpace ambientModel p.val →L[ℂ] TangentSpace 𝓘(ℂ,ChartCoord) p,
      L.comp (mfderiv 𝓘(ℂ,ChartCoord) ambientModel (fun q : Total => q.val) p) =
        ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ,ChartCoord) p) := by
  obtain ⟨⟨r,e⟩,hp⟩ := exists_homeomorphChart_source p
  exact ⟨mfderiv ambientModel 𝓘(ℂ,ChartCoord) (ambientRetraction r e) p.val,
    total_inclusion_mfderiv_chart_leftInverse r e p hp⟩

/-- The joint ambient derivative is injective, including above every exceptional
curve and in the central fibre. No rank or immersion assumption is introduced. -/
theorem total_inclusion_mfderiv_injective (p : Total) :
    Function.Injective (mfderiv 𝓘(ℂ,ChartCoord) ambientModel (fun q : Total => q.val) p) := by
  obtain ⟨L,hL⟩ := total_inclusion_mfderiv_leftInverse p
  have hl : Function.LeftInverse L
      (mfderiv 𝓘(ℂ,ChartCoord) ambientModel (fun q : Total => q.val) p) :=
    fun v => congrArg (fun T => T v) hL
  exact hl.injective

/-- Analytic closed immersion into the actual ambient product, expressed using
its full verified definition: closed embedding, analyticity, and tangent injectivity. -/
theorem total_analytic_closed_immersion :
    IsClosedEmbedding (fun p : Total => p.val) ∧
      ContMDiff 𝓘(ℂ,ChartCoord) ambientModel ω (fun p : Total => p.val) ∧
      ∀ p : Total, Function.Injective
        (mfderiv 𝓘(ℂ,ChartCoord) ambientModel (fun q : Total => q.val) p) :=
  ⟨total_inclusion_isClosedEmbedding,total_inclusion_contMDiff ω,total_inclusion_mfderiv_injective⟩

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence
