import FailureOfSemipositiveMetricExtension.ProjectiveDirectionProduct
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-! Actual tangent maps of the four projections. The default chart of the
product need not choose the same affine frame as the default chart of a factor;
the genuine component derivatives account for this coordinate change. -/
namespace FailureOfSemipositiveMetricExtension.ProjectiveDirectionProduct
noncomputable section
open Set Topology IsManifold
open scoped Manifold ContDiff

def chartTangentEquiv (i : Index) (p : Point) (hp : p ∈ (chart i).source) :
    TangentSpace 𝓘(ℂ,Coord) p ≃L[ℂ] Coord :=
  (mdifferentiable_of_mem_atlas (chart_mem_atlas i)).mfderiv hp

/-- Differentiating a product affine coordinate is exactly differentiating its
factor coordinate after the genuine evaluation map. -/
theorem coordinates_mfderiv_component (i : Index) (p : Point)
    (hp : p ∈ (chart i).source) (r : Fin 4) (v : TangentSpace 𝓘(ℂ,Coord) p) :
    (mfderiv 𝓘(ℂ,Coord) 𝓘(ℂ,Coord) (coordinates i) p v) r =
      mfderiv 𝓘(ℂ) 𝓘(ℂ) (ProjectiveLine.coordinates (i r)) (p r)
        (mfderiv 𝓘(ℂ,Coord) 𝓘(ℂ) (fun q : Point => q r) p v) := by
  have hcoord := ((coordinates_contMDiffOn i 1).contMDiffAt
    ((chart i).open_source.mem_nhds hp)).mdifferentiableAt le_rfl
  have heval := ((eval_contMDiff r 1) p).mdifferentiableAt le_rfl
  have hline := ((GlobalIncidence.lineCoordinates_contMDiffOn (i r) 1).contMDiffAt
    ((ProjectiveLine.chartSet_isOpen (i r)).mem_nhds ((chart_source i ▸ hp) r))).mdifferentiableAt le_rfl
  let pr : Coord →L[ℂ] ℂ := ContinuousLinearMap.proj r
  have hpr : MDifferentiableAt 𝓘(ℂ,Coord) 𝓘(ℂ) pr (coordinates i p) :=
    pr.differentiableAt.mdifferentiableAt
  have hfirst := mfderiv_comp_apply p hpr hcoord v
  have hsecond := mfderiv_comp_apply p hline heval v
  rw [mfderiv_eq_fderiv,ContinuousLinearMap.fderiv] at hfirst
  exact hfirst.symm.trans hsecond

/-- The tuple consists of actual manifold derivatives into each P¹ tangent
space, rather than the raw coordinates of the product tangent vector. -/
def componentDerivative (p : Point) : TangentSpace 𝓘(ℂ,Coord) p →L[ℂ] Coord :=
  ContinuousLinearMap.pi (fun r => mfderiv 𝓘(ℂ,Coord) 𝓘(ℂ) (fun q : Point => q r) p)

@[simp] theorem componentDerivative_apply (p : Point) (v : TangentSpace 𝓘(ℂ,Coord) p) (r : Fin 4) :
    componentDerivative p v r = mfderiv 𝓘(ℂ,Coord) 𝓘(ℂ) (fun q : Point => q r) p v := rfl

/-- All factor derivatives together separate genuine product tangent vectors. -/
theorem componentDerivative_injective (p : Point) : Function.Injective (componentDerivative p) := by
  obtain ⟨i,hp⟩ := charts_cover p
  intro v w hvw
  apply (chartTangentEquiv i p hp).injective
  apply funext
  intro r
  change (mfderiv 𝓘(ℂ,Coord) 𝓘(ℂ,Coord) (coordinates i) p v) r =
    (mfderiv 𝓘(ℂ,Coord) 𝓘(ℂ,Coord) (coordinates i) p w) r
  rw [coordinates_mfderiv_component i p hp r v,coordinates_mfderiv_component i p hp r w]
  exact congrArg (mfderiv 𝓘(ℂ) 𝓘(ℂ) (ProjectiveLine.coordinates (i r)) (p r))
    (congrFun hvw r)

/-- A genuine continuous complex-linear identification with the product of the
four individual projective tangent spaces, including the chart corrections. -/
def componentTangentEquiv (p : Point) : TangentSpace 𝓘(ℂ,Coord) p ≃L[ℂ] Coord := by
  letI : FiniteDimensional ℂ (TangentSpace 𝓘(ℂ,Coord) p) :=
    inferInstanceAs (FiniteDimensional ℂ Coord)
  exact (LinearEquiv.ofBijective (componentDerivative p).toLinearMap
    ⟨componentDerivative_injective p,
      LinearMap.injective_iff_surjective.mp (componentDerivative_injective p)⟩).toContinuousLinearEquiv

@[simp] theorem componentTangentEquiv_apply (p : Point) (v : TangentSpace 𝓘(ℂ,Coord) p) :
    componentTangentEquiv p v = componentDerivative p v := rfl

end
end FailureOfSemipositiveMetricExtension.ProjectiveDirectionProduct
