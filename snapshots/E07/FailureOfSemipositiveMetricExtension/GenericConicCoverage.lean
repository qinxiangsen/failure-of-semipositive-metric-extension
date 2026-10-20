import FailureOfSemipositiveMetricExtension.GenericConicSectionVanishing

/-! Every point with nonvanishing pencil pair and difference belongs to one of
the explicit generic conics. This is direct homogeneous algebra, including the
actual incidence directions, rather than an assumed classification of fibres. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil.Conic
noncomputable section
open Set

def GoodVector (t : ℂ) (w : Fin 3 → ℂ) : Prop :=
  Coordinates.F₁ t (w 0) (w 1) (w 2) ≠ 0 ∧
  Coordinates.F₂ t (w 0) (w 1) (w 2) ≠ 0 ∧
  Coordinates.F₂ t (w 0) (w 1) (w 2) - Coordinates.F₁ t (w 0) (w 1) (w 2) ≠ 0

def dataOfVector (t : ℂ) (ht : t ≠ 0) (w : Fin 3 → ℂ) (hw : GoodVector t w) : Data where
  t := t
  a := Coordinates.F₁ t (w 0) (w 1) (w 2)
  b := Coordinates.F₂ t (w 0) (w 1) (w 2)
  t_ne_zero := ht
  a_ne_zero := hw.1
  b_ne_zero := hw.2.1
  sub_ne_zero := hw.2.2

theorem goodVector_coordinates (t : ℂ) (w : Fin 3 → ℂ) (hw : GoodVector t w) :
    w 0 ≠ 0 ∧ w 1 ≠ 0 ∧ w 1-w 0 ≠ 0 := by
  refine ⟨?_,?_,?_⟩
  · intro h; exact hw.1 (by simp [Coordinates.F₁,h])
  · intro h; exact hw.2.1 (by simp [Coordinates.F₂,h])
  · intro h
    apply hw.2.2
    have he := sub_eq_zero.mp h
    simp [Coordinates.F₁,Coordinates.F₂,he]

theorem goodVector_ne_zero (t : ℂ) (w : Fin 3 → ℂ) (hw : GoodVector t w) : w ≠ 0 := by
  intro h
  exact (goodVector_coordinates t w hw).1 (congrFun h 0)

theorem goodVector_xy_ne_zero (t : ℂ) (w : Fin 3 → ℂ) (hw : GoodVector t w) :
    (![w 0,w 1] : Blowup.Plane) ≠ 0 := by
  intro h
  exact (goodVector_coordinates t w hw).1 (congrFun h 0)

theorem dataOfVector_baseVector (t : ℂ) (ht : t ≠ 0) (w : Fin 3 → ℂ) (hw : GoodVector t w) :
    baseVector (dataOfVector t ht w hw) ![w 0,w 1] =
      (t * w 0 * w 1 * (w 1-w 0)) • w := by
  ext k
  fin_cases k <;> simp [baseVector,denominator,dataOfVector,Coordinates.F₁,Coordinates.F₂] <;> ring

theorem dataOfVector_base (t : ℂ) (ht : t ≠ 0) (w : Fin 3 → ℂ) (hw : GoodVector t w) :
    base (dataOfVector t ht w hw)
      (Projectivization.mk ℂ ![w 0,w 1] (goodVector_xy_ne_zero t w hw)) =
      Projectivization.mk ℂ w (goodVector_ne_zero t w hw) := by
  rw [base_mk]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  exact ⟨t * w 0 * w 1 * (w 1-w 0),(dataOfVector_baseVector t ht w hw).symm⟩

theorem goodVector_away_centre (t : ℂ) (w : Fin 3 → ℂ) (hw : GoodVector t w) (r : Fin 4) :
    Projectivization.mk ℂ w (goodVector_ne_zero t w hw) ≠ centre r t := by
  intro h
  rw [← centre_mk] at h
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
  apply hw.1
  rw [← ha]
  fin_cases r <;> simp [centreVector,Coordinates.p₁,Coordinates.p₂,Coordinates.p₃,Coordinates.p₄,
    Coordinates.F₁] <;> ring <;> simp

/-- Exact reconstruction in the true incidence fibre. All four directions follow
from their proved uniqueness away from the four centres. -/
theorem param_dataOfVector (t : ℂ) (ht : t ≠ 0) (p : Fiber t) (w : Fin 3 → ℂ)
    (hw : GoodVector t w)
    (hp : FixedFiber.blowdown t p = Projectivization.mk ℂ w (goodVector_ne_zero t w hw)) :
    param (dataOfVector t ht w hw)
      (Projectivization.mk ℂ ![w 0,w 1] (goodVector_xy_ne_zero t w hw)) = p := by
  let q := param (dataOfVector t ht w hw)
    (Projectivization.mk ℂ ![w 0,w 1] (goodVector_xy_ne_zero t w hw))
  have hb : FixedFiber.blowdown t q = FixedFiber.blowdown t p :=
    (dataOfVector_base t ht w hw).trans hp.symm
  apply Subtype.ext
  apply Prod.ext
  · exact hb
  · funext r
    apply directions_eq_away (FixedFiber.inclusion t q) (FixedFiber.inclusion t p) r hb rfl
    change FixedFiber.blowdown t q ≠ centre r t
    rw [hb,hp]
    exact goodVector_away_centre t w hw r

def genericLocus (t : ℂ) : Set (Fiber t) :=
  {p | ∃ w : Fin 3 → ℂ, ∃ hw : GoodVector t w,
    FixedFiber.blowdown t p = Projectivization.mk ℂ w (goodVector_ne_zero t w hw)}

/-- Explicit generic conics cover the actual generic locus, with no pencil-fibre
or smoothness-classification theorem as a premise. -/
theorem genericLocus_mem_conic (t : ℂ) (ht : t ≠ 0) (p : Fiber t) (hp : p ∈ genericLocus t) :
    ∃ c : Data, ∃ hct : c.t = t, ∃ d : Direction,
      HEq (param c d) p := by
  obtain ⟨w,hw,hp⟩ := hp
  refine ⟨dataOfVector t ht w hw,rfl,Projectivization.mk ℂ ![w 0,w 1] (goodVector_xy_ne_zero t w hw),?_⟩
  exact heq_of_eq (param_dataOfVector t ht p w hw hp)

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil.Conic
