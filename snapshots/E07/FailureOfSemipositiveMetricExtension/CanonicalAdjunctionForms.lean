import FailureOfSemipositiveMetricExtension.FiberTangentAdjunction

/-! Genuine dt-adjunction on alternating tangent forms. The normal vector has
actual dπ-value 1, and the map is proved independent of its horizontal choice. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalCanonical
noncomputable section
open Set IsManifold Topology
open scoped Manifold ContDiff

def normalVector (i : Fin 4) (e : Fin 2) (p : Total) (hp : p ∈ chartSource i e) :
    TangentSpace 𝓘(ℂ,ChartCoord) p := (chartTangentEquiv i e p hp).symm ((0,0),1)

theorem normalVector_projection (i : Fin 4) (e : Fin 2) (p : Total) (hp : p ∈ chartSource i e) :
    (mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ) projection p) (normalVector i e p hp) = (show ℂ from 1) := by
  rw [projection_mfderiv_coordinates i e p hp]
  change (chartTangentEquiv i e p hp ((chartTangentEquiv i e p hp).symm ((0,0),1))).2 = 1
  rw [ContinuousLinearEquiv.apply_symm_apply]

/-- Contraction with any actual normal vector of parameter differential one
restricts the actual coordinate three-form to the actual fibre two-form. -/
theorem tangentCoordinateForm_contraction (t : ℂ) (i : Fin 4) (e : Fin 2) (p : Fiber t)
    (hp : p ∈ FixedFiber.source t i e)
    (n : TangentSpace 𝓘(ℂ,ChartCoord) (FixedFiber.inclusion t p))
    (hn : (mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ) projection (FixedFiber.inclusion t p)) n = (show ℂ from 1)) :
    ((tangentCoordinateForm i e (FixedFiber.inclusion t p)).curryLeft n).compLinearMap
      (mfderiv 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ,ChartCoord) (FixedFiber.inclusion t) p).toLinearMap =
      FixedFiber.tangentCoordinateForm t i e p := by
  let G := mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ,ChartCoord) (chartCoordinates i e) (FixedFiber.inclusion t p)
  let F := mfderiv 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ,FixedFiber.Coord) (FixedFiber.coordinates t i e) p
  let J := mfderiv 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ,ChartCoord) (FixedFiber.inclusion t) p
  have hn' : (G n).2 = 1 := by
    rw [projection_mfderiv_coordinates i e (FixedFiber.inclusion t p) hp] at hn
    exact hn
  have hJ (v : TangentSpace 𝓘(ℂ,FixedFiber.Coord) p) : G (J v) = (F v,0) := by
    exact congrArg (fun A => A v) (coordinates_mfderiv_inclusion t i e p hp)
  ext v
  change ComplexThreefoldJacobian.coordinateVolume
      (fun j => G ((Matrix.vecCons n (fun k => J (v k))) j)) =
    ComplexSurfaceJacobian.coordinateVolume (fun j => F (v j))
  have he : (fun j => G ((Matrix.vecCons n (fun k => J (v k))) j)) =
      Matrix.vecCons (G n) (fun j => (F (v j),0)) := by
    funext j
    fin_cases j <;> simp [hJ]
  rw [he]
  exact ComplexThreefoldJacobian.coordinateVolume_normal_vertical (G n) hn' (fun j => F (v j))

/-- Contraction/restriction is a genuine linear map between the full intrinsic
cotangent determinant fibres. -/
def adjunctionWithNormal (t : ℂ) (p : Fiber t)
    (n : TangentSpace 𝓘(ℂ,ChartCoord) (FixedFiber.inclusion t p)) :
    CanonicalTangentFiber (FixedFiber.inclusion t p) →ₗ[ℂ] FixedFiber.CanonicalTangentFiber t p where
  toFun f := (f.curryLeft n).compLinearMap
    (mfderiv 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ,ChartCoord) (FixedFiber.inclusion t) p).toLinearMap
  map_add' f g := by ext v; rfl
  map_smul' a f := by ext v; rfl

theorem adjunctionWithNormal_coordinateForm (t : ℂ) (i : Fin 4) (e : Fin 2) (p : Fiber t)
    (hp : p ∈ FixedFiber.source t i e)
    (n : TangentSpace 𝓘(ℂ,ChartCoord) (FixedFiber.inclusion t p))
    (hn : (mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ) projection (FixedFiber.inclusion t p)) n = (show ℂ from 1)) :
    adjunctionWithNormal t p n (tangentCoordinateForm i e (FixedFiber.inclusion t p)) =
      FixedFiber.tangentCoordinateForm t i e p :=
  tangentCoordinateForm_contraction t i e p hp n hn

/-- The map uses dt, not an arbitrary choice of transverse lift: all vectors
whose actual dπ value is 1 give precisely the same map. -/
theorem adjunctionWithNormal_independent (t : ℂ) (p : Fiber t)
    (n n' : TangentSpace 𝓘(ℂ,ChartCoord) (FixedFiber.inclusion t p))
    (hn : (mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ) projection (FixedFiber.inclusion t p)) n = (show ℂ from 1))
    (hn' : (mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ) projection (FixedFiber.inclusion t p)) n' = (show ℂ from 1)) :
    adjunctionWithNormal t p n = adjunctionWithNormal t p n' := by
  obtain ⟨⟨i,e⟩,hp⟩ := FixedFiber.charts_cover t p
  ext f v
  have hf := f.eq_smul_basis_det (tangentBasis i e (FixedFiber.inclusion t p) hp)
  rw [← tangentCoordinateForm_eq_basis_det i e (FixedFiber.inclusion t p) hp] at hf
  rw [hf, map_smul,map_smul,adjunctionWithNormal_coordinateForm t i e p hp n hn,
    adjunctionWithNormal_coordinateForm t i e p hp n' hn']

/-- Canonical dt-adjunction, independent of the chosen local adapted chart. -/
def adjunction (t : ℂ) (p : Fiber t) :
    CanonicalTangentFiber (FixedFiber.inclusion t p) →ₗ[ℂ] FixedFiber.CanonicalTangentFiber t p :=
  let i := (FixedFiber.canonicalCore t).indexAt p
  adjunctionWithNormal t p (normalVector i.1 i.2 (FixedFiber.inclusion t p)
    ((FixedFiber.canonicalCore t).mem_baseSet_at p))

theorem adjunction_coordinateForm (t : ℂ) (i : Fin 4) (e : Fin 2) (p : Fiber t)
    (hp : p ∈ FixedFiber.source t i e) :
    adjunction t p (tangentCoordinateForm i e (FixedFiber.inclusion t p)) =
      FixedFiber.tangentCoordinateForm t i e p := by
  exact adjunctionWithNormal_coordinateForm t i e p hp _ (normalVector_projection _ _ _ _)

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalCanonical
