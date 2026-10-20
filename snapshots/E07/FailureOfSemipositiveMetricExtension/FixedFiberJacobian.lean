import FailureOfSemipositiveMetricExtension.ProjectivePlaneJacobian

/-! Actual two-dimensional fibre chart Jacobians, with the blow-down chain rule.
All differentiations are of the existing eight partial homeomorphisms. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiber
noncomputable section
open Set Topology
open ComplexSurfaceJacobian
open scoped Manifold ContDiff

def baseMap (t : ℂ) (r : Fin 4) (e : Fin 2) (q : Coord) : Coord :=
  baseCoordinates r t (Blowup.projection (localParam e q))

theorem baseMap_hasFDerivAt (t : ℂ) (r : Fin 4) (e : Fin 2) (q : Coord) :
    HasFDerivAt (baseMap t r e) (blowdownDerivative e q) q := by
  fin_cases r <;> fin_cases e
  · exact blowdown_hasFDerivAt 0 q
  · exact blowdown_hasFDerivAt 1 q
  · exact blowdown_hasFDerivAt 0 q
  · exact blowdown_hasFDerivAt 1 q
  · exact (blowdown_hasFDerivAt 0 q).const_add (1,t)
  · exact (blowdown_hasFDerivAt 1 q).const_add (1,t)
  · exact blowdown_hasFDerivAt 0 q
  · exact blowdown_hasFDerivAt 1 q

theorem baseMap_jacobian (t : ℂ) (r : Fin 4) (e : Fin 2) (q : Coord) :
    jacobian (baseMap t r e) q = directionSign e * q.1 := by
  rw [jacobian,(baseMap_hasFDerivAt t r e q).fderiv]
  simpa only [jacobian,(blowdown_hasFDerivAt e q).fderiv] using blowdown_jacobian e q

theorem blowdown_param_baseMap (t : ℂ) (r : Fin 4) (e : Fin 2) (q : Coord) :
    blowdown t (param t r e q) = ProjectivePlane.param (baseChart r) (baseMap t r e q) :=
  affineBase_eq_param r t _

theorem baseMap_coordinates (t : ℂ) (r : Fin 4) (e : Fin 2) (p : Fiber t)
    (hp : p ∈ source t r e) :
    baseMap t r e (coordinates t r e p) = ProjectivePlane.coordinates (baseChart r) (blowdown t p) := by
  have h := blowdown_param_baseMap t r e (coordinates t r e p)
  rw [param_coordinates t r e p hp] at h
  rw [h,ProjectivePlane.coordinates_param]

def change (t : ℂ) (i j : Fin 4) (e f : Fin 2) : Coord → Coord :=
  coordinates t j f ∘ param t i e

def changeDomain (t : ℂ) (i j : Fin 4) (e f : Fin 2) : Set Coord :=
  ((chart t i e).symm.trans (chart t j f)).source

theorem changeDomain_isOpen (t : ℂ) (i j : Fin 4) (e f : Fin 2) :
    IsOpen (changeDomain t i j e f) := ((chart t i e).symm.trans (chart t j f)).open_source

theorem change_contDiffOn (t : ℂ) (i j : Fin 4) (e f : Fin 2) (n : WithTop ℕ∞) :
    ContDiffOn ℂ n (change t i j e f) (changeDomain t i j e f) :=
  transition_contDiffOn t i j e f n

theorem change_differentiableAt (t : ℂ) (i j : Fin 4) (e f : Fin 2) (q : Coord)
    (hq : q ∈ changeDomain t i j e f) : DifferentiableAt ℂ (change t i j e f) q :=
  ((change_contDiffOn t i j e f 1).contDiffAt ((changeDomain_isOpen t i j e f).mem_nhds hq)).differentiableAt (by norm_num)

theorem change_baseMap (t : ℂ) (i j : Fin 4) (e f : Fin 2) (q : Coord)
    (hq : q ∈ changeDomain t i j e f) :
    baseMap t j f (change t i j e f q) =
      ProjectivePlane.transition (baseChart i) (baseChart j) (baseMap t i e q) := by
  have hp : param t i e q ∈ source t j f := hq.2
  rw [change,Function.comp_apply,baseMap_coordinates t j f _ hp,blowdown_param_baseMap]
  apply ProjectivePlane.coordinates_transition
  apply (ProjectivePlane.param_mem_chartSet_iff _ _ _).mp
  rw [← blowdown_param_baseMap]
  exact ((mem_chartSource_iff j f (inclusion t (param t i e q))).mp hp).1

/-- The derivative chain rule before cancellation at the exceptional divisor. -/
theorem change_jacobian_blowdown (t : ℂ) (i j : Fin 4) (e f : Fin 2) (q : Coord)
    (hq : q ∈ changeDomain t i j e f) :
    (directionSign f * (change t i j e f q).1) * jacobian (change t i j e f) q =
      (planeSign (baseChart i) * planeSign (baseChart j) *
        (ProjectivePlane.vector (baseChart i) (baseMap t i e q) (baseChart j) ^ 3)⁻¹) *
          (directionSign e * q.1) := by
  have ho : baseMap t i e q ∈ ProjectivePlane.overlap (baseChart i) (baseChart j) := by
    apply (ProjectivePlane.param_mem_chartSet_iff _ _ _).mp
    rw [← blowdown_param_baseMap]
    exact ((mem_chartSource_iff j f (inclusion t (param t i e q))).mp hq.2).1
  have hp : DifferentiableAt ℂ (ProjectivePlane.transition (baseChart i) (baseChart j)) (baseMap t i e q) :=
    ((ProjectivePlane.transition_contDiffOn _ _ 1).contDiffAt
      ((ProjectivePlane.overlap_isOpen _ _).mem_nhds ho)).differentiableAt (by norm_num)
  have heq : (baseMap t j f ∘ change t i j e f) =ᶠ[𝓝 q]
      (ProjectivePlane.transition (baseChart i) (baseChart j) ∘ baseMap t i e) := by
    filter_upwards [(changeDomain_isOpen t i j e f).mem_nhds hq] with w hw
    exact change_baseMap t i j e f w hw
  have h := congrArg determinant (heq.fderiv_eq (𝕜 := ℂ))
  change jacobian (baseMap t j f ∘ change t i j e f) q =
    jacobian (ProjectivePlane.transition (baseChart i) (baseChart j) ∘ baseMap t i e) q at h
  rw [jacobian_comp q (change_differentiableAt t i j e f q hq)
    (baseMap_hasFDerivAt t j f _).differentiableAt,
    jacobian_comp q (baseMap_hasFDerivAt t i e q).differentiableAt hp,
    baseMap_jacobian,baseMap_jacobian,plane_transition_jacobian _ _ _ ho] at h
  exact h

theorem change_jacobian_contDiffOn (t : ℂ) (i j : Fin 4) (e f : Fin 2) :
    ContDiffOn ℂ ω (jacobian (change t i j e f)) (changeDomain t i j e f) :=
  jacobian_contDiffOn (change_contDiffOn t i j e f ω) (changeDomain_isOpen t i j e f)

theorem change_inverse (t : ℂ) (i j : Fin 4) (e f : Fin 2) (q : Coord)
    (hq : q ∈ changeDomain t i j e f) :
    change t j i f e (change t i j e f q) = q := by
  change coordinates t i e (param t j f (coordinates t j f (param t i e q))) = q
  rw [param_coordinates t j f (param t i e q) hq.2,coordinates_param]

theorem change_mem_reverse (t : ℂ) (i j : Fin 4) (e f : Fin 2) (q : Coord)
    (hq : q ∈ changeDomain t i j e f) : change t i j e f q ∈ changeDomain t j i f e := by
  constructor
  · exact (chart t j f).map_source hq.2
  · change param t j f (coordinates t j f (param t i e q)) ∈ source t i e
    rw [param_coordinates t j f (param t i e q) hq.2]
    exact (chart t i e).map_target hq.1

/-- Opposite genuine chart Jacobians multiply to one. -/
theorem change_jacobian_inverse (t : ℂ) (i j : Fin 4) (e f : Fin 2) (q : Coord)
    (hq : q ∈ changeDomain t i j e f) :
    jacobian (change t j i f e) (change t i j e f q) * jacobian (change t i j e f) q = 1 := by
  have heq : (change t j i f e ∘ change t i j e f) =ᶠ[𝓝 q] id := by
    filter_upwards [(changeDomain_isOpen t i j e f).mem_nhds hq] with w hw
    exact change_inverse t i j e f w hw
  have h := congrArg determinant (heq.fderiv_eq (𝕜 := ℂ))
  change jacobian (change t j i f e ∘ change t i j e f) q = jacobian id q at h
  rw [jacobian_comp q (change_differentiableAt t i j e f q hq)
    (change_differentiableAt t j i f e _ (change_mem_reverse t i j e f q hq)),jacobian_id] at h
  exact h

theorem change_jacobian_ne_zero (t : ℂ) (i j : Fin 4) (e f : Fin 2) (q : Coord)
    (hq : q ∈ changeDomain t i j e f) : jacobian (change t i j e f) q ≠ 0 :=
  right_ne_zero_of_mul_eq_one (change_jacobian_inverse t i j e f q hq)

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiber
