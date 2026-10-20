import FailureOfSemipositiveMetricExtension.FixedFiberCanonicalAdjoint
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! The Jacobian canonical line is identified, fibre by fibre and in every chart,
with the full space of alternating complex two-forms on the actual manifold tangent
space.  The formulas use the installed manifold derivative, not formal coordinate
symbols or a postulated canonical-class identification. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiber
noncomputable section
open Set Bundle IsManifold Topology ComplexSurfaceJacobian
open scoped Manifold ContDiff

/-- The derivative of an actual surface chart, as a linear isomorphism. -/
def chartTangentEquiv (t : ℂ) (i : Fin 4) (e : Fin 2) (p : Fiber t)
    (hp : p ∈ source t i e) : TangentSpace 𝓘(ℂ,Coord) p ≃L[ℂ] Coord :=
  (mdifferentiable_of_mem_atlas (chart_mem_atlas t i e)).mfderiv hp

/-- Ordered coordinate volume, pulled back to the genuine tangent space. -/
def tangentCoordinateForm (t : ℂ) (i : Fin 4) (e : Fin 2) (p : Fiber t) :
    (TangentSpace 𝓘(ℂ,Coord) p) [⋀^Fin 2]→ₗ[ℂ] ℂ :=
  coordinateVolume.compLinearMap (mfderiv 𝓘(ℂ,Coord) 𝓘(ℂ,Coord) (coordinates t i e) p).toLinearMap

def tangentBasis (t : ℂ) (i : Fin 4) (e : Fin 2) (p : Fiber t)
    (hp : p ∈ source t i e) : Basis (Fin 2) ℂ (TangentSpace 𝓘(ℂ,Coord) p) :=
  (Basis.finTwoProd ℂ).map (chartTangentEquiv t i e p hp).symm.toLinearEquiv

theorem tangentCoordinateForm_eq_basis_det (t : ℂ) (i : Fin 4) (e : Fin 2) (p : Fiber t)
    (hp : p ∈ source t i e) : tangentCoordinateForm t i e p = (tangentBasis t i e p hp).det := by
  rw [tangentBasis,Basis.det_map']
  rfl

theorem tangentCoordinateForm_ne_zero (t : ℂ) (i : Fin 4) (e : Fin 2) (p : Fiber t)
    (hp : p ∈ source t i e) : tangentCoordinateForm t i e p ≠ 0 := by
  rw [tangentCoordinateForm_eq_basis_det t i e p hp]
  exact Basis.det_ne_zero _

/-- The chain rule for the installed charts, on their actual tangent spaces. -/
theorem coordinates_mfderiv_change (t : ℂ) (i j : Fin 4) (e f : Fin 2) (p : Fiber t)
    (hi : p ∈ source t i e) (hj : p ∈ source t j f) :
    mfderiv 𝓘(ℂ,Coord) 𝓘(ℂ,Coord) (coordinates t j f) p =
      (fderiv ℂ (change t i j e f) (coordinates t i e p)).comp
        (mfderiv 𝓘(ℂ,Coord) 𝓘(ℂ,Coord) (coordinates t i e) p) := by
  have heq : (change t i j e f ∘ coordinates t i e) =ᶠ[𝓝 p] coordinates t j f := by
    filter_upwards [(source_isOpen t i e).mem_nhds hi] with q hq
    change coordinates t j f (param t i e (coordinates t i e q)) = _
    rw [param_coordinates t i e q hq]
  have hc := (change_differentiableAt t i j e f (coordinates t i e p)
    (coordinates_mem_changeDomain t i j e f p hi hj)).mdifferentiableAt
  have hi' : MDifferentiableAt 𝓘(ℂ,Coord) 𝓘(ℂ,Coord) (coordinates t i e) p :=
    (mdifferentiable_of_mem_atlas (chart_mem_atlas t i e)).mdifferentiableAt hi
  rw [← heq.mfderiv_eq, mfderiv_comp p hc hi', mfderiv_eq_fderiv]

/-- Forward chart changes pull back the target volume by their forward determinant. -/
theorem tangentCoordinateForm_change (t : ℂ) (i j : Fin 4) (e f : Fin 2) (p : Fiber t)
    (hi : p ∈ source t i e) (hj : p ∈ source t j f) :
    tangentCoordinateForm t j f p = chartJacobian t i j e f p • tangentCoordinateForm t i e p := by
  rw [tangentCoordinateForm,coordinates_mfderiv_change t i j e f p hi hj]
  ext v
  exact Basis.det_comp (Basis.finTwoProd ℂ)
    (fderiv ℂ (change t i j e f) (coordinates t i e p)).toLinearMap
    ((mfderiv 𝓘(ℂ,Coord) 𝓘(ℂ,Coord) (coordinates t i e) p).toLinearMap ∘ v)

/-- Scalar coefficients transform in the reverse direction, exactly as canonicalCore. -/
theorem tangentCoordinateForm_canonicalGain (t : ℂ) (i j : CanonicalIndex) (p : Fiber t)
    (hi : p ∈ source t i.1 i.2) (hj : p ∈ source t j.1 j.2) :
    tangentCoordinateForm t i.1 i.2 p = canonicalGain t i j p • tangentCoordinateForm t j.1 j.2 p :=
  tangentCoordinateForm_change t j.1 i.1 j.2 i.2 p hj hi

/-- The full cotangent determinant fibre, realized as all alternating top-degree forms. -/
abbrev CanonicalTangentFiber (t : ℂ) (p : Fiber t) :=
  (TangentSpace 𝓘(ℂ,Coord) p) [⋀^Fin 2]→ₗ[ℂ] ℂ

/-- A linear equivalence onto all genuine alternating tangent two-forms. -/
def canonicalFiberFormEquiv (t : ℂ) (p : Fiber t) :
    (canonicalCore t).Fiber p ≃ₗ[ℂ] CanonicalTangentFiber t p := by
  let i := (canonicalCore t).indexAt p
  let B := tangentBasis t i.1 i.2 p ((canonicalCore t).mem_baseSet_at p)
  exact
    { toFun := fun z => (show ℂ from z) • B.det
      invFun := fun f => f B
      left_inv := fun z => by
        change (show ℂ from z) * B.det B = z
        rw [Basis.det_self,mul_one]
      right_inv := fun f => (f.eq_smul_basis_det B).symm
      map_add' := fun x y => add_smul (show ℂ from x) (show ℂ from y) B.det
      map_smul' := fun a z => smul_assoc a (show ℂ from z) B.det }

@[simp] theorem canonicalFiberFormEquiv_apply (t : ℂ) (p : Fiber t) (v : (canonicalCore t).Fiber p) :
    canonicalFiberFormEquiv t p v = (show ℂ from v) •
      tangentCoordinateForm t ((canonicalCore t).indexAt p).1 ((canonicalCore t).indexAt p).2 p := by
  rw [tangentCoordinateForm_eq_basis_det t _ _ p ((canonicalCore t).mem_baseSet_at p)]
  rfl

/-- In every chart, the intrinsic form is its actual bundle coordinate times the
coordinate volume on the tangent space. -/
theorem canonicalFiberFormEquiv_localTriv (t : ℂ) (i : CanonicalIndex) (p : Fiber t)
    (v : (canonicalCore t).Fiber p) (hp : p ∈ source t i.1 i.2) :
    canonicalFiberFormEquiv t p v =
      ((canonicalCore t).localTriv i ⟨p,v⟩).2 • tangentCoordinateForm t i.1 i.2 p := by
  rw [canonicalFiberFormEquiv_apply,VectorBundleCore.localTriv_apply]
  rw [tangentCoordinateForm_canonicalGain t ((canonicalCore t).indexAt p) i p
    ((canonicalCore t).mem_baseSet_at p) hp]
  change (show ℂ from v) • (canonicalGain t ((canonicalCore t).indexAt p) i p • _) =
    (canonicalGain t ((canonicalCore t).indexAt p) i p * (show ℂ from v)) • _
  rw [smul_smul,mul_comm]

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiber

namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold
open scoped Manifold ContDiff

/-- The actual ambient (1;-1,-1,-1,-1) fibre is the full cotangent determinant fibre. -/
def ambientCanonicalFormEquiv (t : ℂ) (p : Fiber t) :
    (kCore t).Fiber p ≃ₗ[ℂ] FixedFiber.CanonicalTangentFiber t p :=
  (canonicalFiberEquiv t p).toLinearEquiv.trans (FixedFiber.canonicalFiberFormEquiv t p)

/-- The previously constructed analytic bundle isomorphism has its claimed
intrinsic two-form meaning, in every refined coordinate chart. -/
theorem ambientCanonicalFormEquiv_localTriv (t : ℂ) (d : DivisionIndex) (p : Fiber t)
    (v : (kCore t).Fiber p) (hp : p ∈ divisionPatch t d) :
    ambientCanonicalFormEquiv t p v =
      (canonicalFactor t d p * ((kCore t).localTriv (divisionFrame d) ⟨p,v⟩).2) •
        FixedFiber.tangentCoordinateForm t d.1 d.2.1 p := by
  change FixedFiber.canonicalFiberFormEquiv t p (canonicalFiberEquiv t p v) = _
  rw [FixedFiber.canonicalFiberFormEquiv_localTriv t (divisionChart d) p _ hp.1]
  have h := congrArg Prod.snd (canonicalBundleEquiv_localTriv t d ⟨p,v⟩ hp)
  exact congrArg (fun z : ℂ => z • FixedFiber.tangentCoordinateForm t d.1 d.2.1 p) h

/-- The intrinsic nowhere-zero form corresponding to an ambient local K frame. -/
def ambientFrameTangentForm (t : ℂ) (d : DivisionIndex) (p : Fiber t) :
    FixedFiber.CanonicalTangentFiber t p :=
  canonicalFactor t d p • FixedFiber.tangentCoordinateForm t d.1 d.2.1 p

theorem ambientFrameTangentForm_ne_zero (t : ℂ) (d : DivisionIndex) (p : Fiber t)
    (hp : p ∈ divisionPatch t d) : ambientFrameTangentForm t d p ≠ 0 :=
  smul_ne_zero (canonicalFactor_ne_zero t d p hp)
    (FixedFiber.tangentCoordinateForm_ne_zero t d.1 d.2.1 p hp.1)

/-- This is the genuine cotangent-determinant frame law, including the transition
orientation and the scalar factor connecting the specific ambient degree model. -/
theorem ambientFrameTangentForm_transition (t : ℂ) (d c : DivisionIndex) (p : Fiber t)
    (hd : p ∈ divisionPatch t d) (hc : p ∈ divisionPatch t c) :
    gain t 1 (fun _ => -1) (divisionFrame d) (divisionFrame c) p •
      ambientFrameTangentForm t c p = ambientFrameTangentForm t d p := by
  unfold ambientFrameTangentForm
  have h : FixedFiber.tangentCoordinateForm t d.1 d.2.1 p =
      FixedFiber.canonicalGain t (divisionChart d) (divisionChart c) p •
        FixedFiber.tangentCoordinateForm t c.1 c.2.1 p :=
    FixedFiber.tangentCoordinateForm_canonicalGain t (divisionChart d) (divisionChart c) p hd.1 hc.1
  rw [h]
  rw [smul_smul,smul_smul]
  congr 1
  exact (canonicalFactor_transition t d c p hd hc).symm.trans (mul_comm _ _)

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
