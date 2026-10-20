import FailureOfSemipositiveMetricExtension.GlobalCanonicalAtlas

/-! Intrinsic tangent-three-form semantics for the actual total-space canonical
bundle, in every genuine chart. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalCanonical
noncomputable section
open Set Bundle IsManifold Topology ComplexThreefoldJacobian
open scoped Manifold ContDiff

def chartTangentEquiv (i : Fin 4) (e : Fin 2) (p : Total) (hp : p ∈ chartSource i e) :
    TangentSpace 𝓘(ℂ,ChartCoord) p ≃L[ℂ] ChartCoord :=
  (mdifferentiable_of_mem_atlas (show homeomorphChart i e ∈ atlas ChartCoord Total from
    (mem_atlas_iff _).mpr ⟨i,e,rfl⟩)).mfderiv hp

def tangentCoordinateForm (i : Fin 4) (e : Fin 2) (p : Total) :
    (TangentSpace 𝓘(ℂ,ChartCoord) p) [⋀^Fin 3]→ₗ[ℂ] ℂ :=
  coordinateVolume.compLinearMap
    (mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ,ChartCoord) (chartCoordinates i e) p).toLinearMap

def tangentBasis (i : Fin 4) (e : Fin 2) (p : Total) (hp : p ∈ chartSource i e) :
    Basis (Fin 3) ℂ (TangentSpace 𝓘(ℂ,ChartCoord) p) :=
  coordinateBasis.map (chartTangentEquiv i e p hp).symm.toLinearEquiv

theorem tangentCoordinateForm_eq_basis_det (i : Fin 4) (e : Fin 2) (p : Total)
    (hp : p ∈ chartSource i e) : tangentCoordinateForm i e p = (tangentBasis i e p hp).det := by
  rw [tangentBasis,Basis.det_map']
  rfl

theorem tangentCoordinateForm_ne_zero (i : Fin 4) (e : Fin 2) (p : Total)
    (hp : p ∈ chartSource i e) : tangentCoordinateForm i e p ≠ 0 := by
  rw [tangentCoordinateForm_eq_basis_det i e p hp]
  exact Basis.det_ne_zero _

theorem coordinates_mfderiv_change (i j : Fin 4) (e f : Fin 2) (p : Total)
    (hi : p ∈ chartSource i e) (hj : p ∈ chartSource j f) :
    mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ,ChartCoord) (chartCoordinates j f) p =
      (fderiv ℂ (change i j e f) (chartCoordinates i e p)).comp
        (mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ,ChartCoord) (chartCoordinates i e) p) := by
  have heq : (change i j e f ∘ chartCoordinates i e) =ᶠ[𝓝 p] chartCoordinates j f := by
    filter_upwards [(chartSource_isOpen i e).mem_nhds hi] with q hq
    change chartCoordinates j f (chartParam i e (chartCoordinates i e q)) = _
    rw [chartParam_coordinates i e q hq]
  have hc := (change_differentiableAt i j e f (chartCoordinates i e p)
    (coordinates_mem_changeDomain i j e f p hi hj)).mdifferentiableAt
  have hi' : MDifferentiableAt 𝓘(ℂ,ChartCoord) 𝓘(ℂ,ChartCoord) (chartCoordinates i e) p :=
    ((chartCoordinates_contMDiffOn i e 1).contMDiffAt ((chartSource_isOpen i e).mem_nhds hi)).mdifferentiableAt le_rfl
  rw [← heq.mfderiv_eq,mfderiv_comp p hc hi',mfderiv_eq_fderiv]

theorem tangentCoordinateForm_change (i j : Fin 4) (e f : Fin 2) (p : Total)
    (hi : p ∈ chartSource i e) (hj : p ∈ chartSource j f) :
    tangentCoordinateForm j f p = chartJacobian i j e f p • tangentCoordinateForm i e p := by
  rw [tangentCoordinateForm,coordinates_mfderiv_change i j e f p hi hj]
  ext v
  exact Basis.det_comp coordinateBasis
    (fderiv ℂ (change i j e f) (chartCoordinates i e p)).toLinearMap
    ((mfderiv 𝓘(ℂ,ChartCoord) 𝓘(ℂ,ChartCoord) (chartCoordinates i e) p).toLinearMap ∘ v)

theorem tangentCoordinateForm_canonicalGain (i j : Index) (p : Total)
    (hi : p ∈ chartSource i.1 i.2) (hj : p ∈ chartSource j.1 j.2) :
    tangentCoordinateForm i.1 i.2 p = canonicalGain i j p • tangentCoordinateForm j.1 j.2 p :=
  tangentCoordinateForm_change j.1 i.1 j.2 i.2 p hj hi

abbrev CanonicalTangentFiber (p : Total) := (TangentSpace 𝓘(ℂ,ChartCoord) p) [⋀^Fin 3]→ₗ[ℂ] ℂ

def canonicalFiberFormEquiv (p : Total) : canonicalCore.Fiber p ≃ₗ[ℂ] CanonicalTangentFiber p := by
  let i := canonicalCore.indexAt p
  let B := tangentBasis i.1 i.2 p (canonicalCore.mem_baseSet_at p)
  exact
    { toFun := fun z => (show ℂ from z) • B.det
      invFun := fun f => f B
      left_inv := fun z => by
        change (show ℂ from z) * B.det B = z
        rw [Basis.det_self,mul_one]
      right_inv := fun f => (f.eq_smul_basis_det B).symm
      map_add' := fun x y => add_smul (show ℂ from x) (show ℂ from y) B.det
      map_smul' := fun a z => smul_assoc a (show ℂ from z) B.det }

@[simp] theorem canonicalFiberFormEquiv_apply (p : Total) (v : canonicalCore.Fiber p) :
    canonicalFiberFormEquiv p v = (show ℂ from v) •
      tangentCoordinateForm (canonicalCore.indexAt p).1 (canonicalCore.indexAt p).2 p := by
  rw [tangentCoordinateForm_eq_basis_det _ _ p (canonicalCore.mem_baseSet_at p)]
  rfl

theorem canonicalFiberFormEquiv_localTriv (i : Index) (p : Total)
    (v : canonicalCore.Fiber p) (hp : p ∈ chartSource i.1 i.2) :
    canonicalFiberFormEquiv p v =
      (canonicalCore.localTriv i ⟨p,v⟩).2 • tangentCoordinateForm i.1 i.2 p := by
  rw [canonicalFiberFormEquiv_apply,VectorBundleCore.localTriv_apply]
  rw [tangentCoordinateForm_canonicalGain (canonicalCore.indexAt p) i p
    (canonicalCore.mem_baseSet_at p) hp]
  change (show ℂ from v) • (canonicalGain (canonicalCore.indexAt p) i p • _) =
    (canonicalGain (canonicalCore.indexAt p) i p * (show ℂ from v)) • _
  rw [smul_smul,mul_comm]

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalCanonical
