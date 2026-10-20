import FailureOfSemipositiveMetricExtension.GenericConicAlgebra

/-! The homogeneous conic parametrization is promoted to the actual projective
quotients and the actual incidence fibre. Every exceptional direction is included. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil.Conic
noncomputable section
open Set

/-- The degree-two map to the actual projective plane. Its representative-free
normalization law is proved below before any regularity is claimed. -/
def base (c : Data) (d : Direction) : PlanePoint :=
  Projectivization.mk ℂ (baseVector c d.rep) (baseVector_ne_zero c d.rep d.rep_nonzero)

theorem base_mk (c : Data) (v : Blowup.Plane) (hv : v ≠ 0) :
    base c (Projectivization.mk ℂ v hv) = Projectivization.mk ℂ (baseVector c v) (baseVector_ne_zero c v hv) := by
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  change (a : ℂ) • v = (Projectivization.mk ℂ v hv).rep at ha
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨(a : ℂ)^2,?_⟩
  rw [← baseVector_smul,ha]

/-- All four direction maps are projectivizations of explicitly injective linear maps. -/
def direction (c : Data) (r : Fin 4) : Direction → Direction :=
  Projectivization.map (directionMap c r) (directionMap_injective c r)

theorem direction_mk (c : Data) (r : Fin 4) (v : Blowup.Plane) (hv : v ≠ 0) :
    direction c r (Projectivization.mk ℂ v hv) =
      Projectivization.mk ℂ (directionMap c r v) (directionMap_ne_zero c r v hv) := rfl

@[simp] theorem direction_three (c : Data) (d : Direction) : direction c 3 d = d := by
  induction d using Projectivization.ind with
  | h v hv => rw [direction_mk]; rfl

theorem incidence (c : Data) (d : Direction) (r : Fin 4) :
    Incidence (base c d) (direction c r d) r c.t := by
  induction d using Projectivization.ind with
  | h v hv =>
    rw [base_mk,direction_mk,incidence_mk_iff,Projectivization.submodule_mk,Submodule.mem_span_singleton]
    exact ⟨incidenceFactor c r v,(pairMap_baseVector c r v).symm⟩

/-- A genuine global P1 parametrization into the fixed incidence surface. -/
def param (c : Data) (d : Direction) : Fiber c.t :=
  ⟨(base c d,fun r => direction c r d),incidence c d⟩

@[simp] theorem param_blowdown (c : Data) (d : Direction) : FixedFiber.blowdown c.t (param c d) = base c d := rfl
@[simp] theorem param_direction (c : Data) (r : Fin 4) (d : Direction) :
    FixedFiber.direction c.t r (param c d) = direction c r d := rfl

/-- The fourth direction is exactly the original projective parameter, including
at the fourth exceptional intersection point. -/
@[simp] theorem param_direction_three (c : Data) (d : Direction) :
    FixedFiber.direction c.t 3 (param c d) = d := direction_three c d

theorem param_injective (c : Data) : Function.Injective (param c) := by
  intro d e h
  simpa only [param_direction_three] using congrArg (FixedFiber.direction c.t 3) h

/-- The value of the pencil corresponding to this nondegenerate conic. -/
def pencilValue (c : Data) : ProjectiveLine.Point := ProjectiveLine.vectorPoint ![c.a,c.b]

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil.Conic
