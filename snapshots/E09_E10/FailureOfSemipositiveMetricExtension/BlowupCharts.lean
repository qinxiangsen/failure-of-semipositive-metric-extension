import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic

/-!
The incidence model of the blow-up of the affine plane at the origin, its two
bijective set charts, and the differentiability of their transition map.
The points and directions use mathlib's actual projectivization quotient.
This file does not assert that a complex manifold structure has been installed.
-/

namespace FailureOfSemipositiveMetricExtension.Blowup

noncomputable section

abbrev Plane := Fin 2 → ℂ
abbrev Direction := Projectivization ℂ Plane

/-- The incidence variety: the affine point belongs to its specified line. -/
def Point := {p : Plane × Direction // p.1 ∈ p.2.submodule}

def projection (p : Point) : Plane := p.val.1
def direction (p : Point) : Direction := p.val.2

@[ext] theorem point_ext {p q : Point}
    (hp : projection p = projection q) (hd : direction p = direction q) : p = q :=
  Subtype.ext (Prod.ext hp hd)

def vectorX (s : ℂ) : Plane := ![1,s]
def vectorY (s : ℂ) : Plane := ![s,1]

theorem vectorX_ne_zero (s : ℂ) : vectorX s ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simpa [vectorX] using h0

theorem vectorY_ne_zero (s : ℂ) : vectorY s ≠ 0 := by
  intro h
  have h1 := congrFun h 1
  simpa [vectorY] using h1

def lineX (s : ℂ) : Direction := Projectivization.mk ℂ (vectorX s) (vectorX_ne_zero s)
def lineY (s : ℂ) : Direction := Projectivization.mk ℂ (vectorY s) (vectorY_ne_zero s)

/-- First affine parametrization: `(r,s) ↦ ((r,r*s),[1:s])`. -/
def X (r s : ℂ) : Point :=
  ⟨(![r,r*s], lineX s), by
    rw [lineX, Projectivization.submodule_mk]
    apply Submodule.mem_span_singleton.mpr
    refine ⟨r, ?_⟩
    ext i; fin_cases i <;> simp [vectorX]⟩

/-- Second affine parametrization: `(r,s) ↦ ((r*s,r),[s:1])`. -/
def Y (r s : ℂ) : Point :=
  ⟨(![r*s,r], lineY s), by
    rw [lineY, Projectivization.submodule_mk]
    apply Submodule.mem_span_singleton.mpr
    refine ⟨r, ?_⟩
    ext i; fin_cases i <;> simp [vectorY]⟩

@[simp] theorem projection_X (r s : ℂ) : projection (X r s) = ![r,r*s] := rfl
@[simp] theorem projection_Y (r s : ℂ) : projection (Y r s) = ![r*s,r] := rfl
@[simp] theorem direction_X (r s : ℂ) : direction (X r s) = lineX s := rfl
@[simp] theorem direction_Y (r s : ℂ) : direction (Y r s) = lineY s := rfl

theorem lineX_injective : Function.Injective lineX := by
  intro s t h
  rcases (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h with ⟨a,ha⟩
  have h0 := congrFun ha 0
  have h1 := congrFun ha 1
  simp [vectorX] at h0 h1
  simpa [h0] using h1.symm

theorem lineY_injective : Function.Injective lineY := by
  intro s t h
  rcases (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h with ⟨a,ha⟩
  have h0 := congrFun ha 0
  have h1 := congrFun ha 1
  simp [vectorY] at h0 h1
  simpa [h1] using h0.symm

theorem X_injective : Function.Injective (fun q : ℂ × ℂ => X q.1 q.2) := by
  intro q q' h
  apply Prod.ext
  · have h0 := congrArg (fun p => projection p 0) h
    simpa [projection, X] using h0
  · exact lineX_injective (congrArg direction h)

theorem Y_injective : Function.Injective (fun q : ℂ × ℂ => Y q.1 q.2) := by
  intro q q' h
  apply Prod.ext
  · have h1 := congrArg (fun p => projection p 1) h
    simpa [projection, Y] using h1
  · exact lineY_injective (congrArg direction h)

/-- Every projective direction has at least one of the two affine normalizations. -/
theorem direction_cover (d : Direction) :
    (∃ s, d = lineX s) ∨ (∃ s, d = lineY s) := by
  by_cases h0 : d.rep 0 = 0
  · have h1 : d.rep 1 ≠ 0 := by
      intro h1
      apply d.rep_nonzero
      ext i; fin_cases i <;> simp [h0,h1]
    right
    refine ⟨d.rep 0 / d.rep 1, ?_⟩
    rw [← d.mk_rep]
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    refine ⟨d.rep 1, ?_⟩
    ext i; fin_cases i <;> simp [vectorY, mul_div_cancel₀, h1]
  · left
    refine ⟨d.rep 1 / d.rep 0, ?_⟩
    rw [← d.mk_rep]
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    refine ⟨d.rep 0, ?_⟩
    ext i; fin_cases i <;> simp [vectorX, mul_div_cancel₀, h0]

theorem eq_X_of_direction (p : Point) (s : ℂ) (h : direction p = lineX s) :
    p = X (projection p 0) s := by
  have hm : projection p ∈ (lineX s).submodule := by
    rw [← h]; exact p.property
  rw [lineX, Projectivization.submodule_mk, Submodule.mem_span_singleton] at hm
  rcases hm with ⟨a,ha⟩
  apply point_ext
  · rw [projection_X, ← ha]
    ext i; fin_cases i <;> simp [vectorX]
  · exact h

theorem eq_Y_of_direction (p : Point) (s : ℂ) (h : direction p = lineY s) :
    p = Y (projection p 1) s := by
  have hm : projection p ∈ (lineY s).submodule := by
    rw [← h]; exact p.property
  rw [lineY, Projectivization.submodule_mk, Submodule.mem_span_singleton] at hm
  rcases hm with ⟨a,ha⟩
  apply point_ext
  · rw [projection_Y, ← ha]
    ext i; fin_cases i <;> simp [vectorY]
  · exact h

/-- The two explicitly constructed affine parametrizations cover every incidence point. -/
theorem charts_cover (p : Point) :
    (∃ r s, p = X r s) ∨ (∃ r s, p = Y r s) := by
  rcases direction_cover (direction p) with ⟨s,hs⟩ | ⟨s,hs⟩
  · exact Or.inl ⟨projection p 0,s,eq_X_of_direction p s hs⟩
  · exact Or.inr ⟨projection p 1,s,eq_Y_of_direction p s hs⟩

/-- Intrinsic set domains specified by the projective direction. -/
def chartXSet : Set Point := {p | ∃ s, direction p = lineX s}
def chartYSet : Set Point := {p | ∃ s, direction p = lineY s}

theorem chartXSet_eq_range : chartXSet = Set.range (fun q : ℂ × ℂ => X q.1 q.2) := by
  ext p
  constructor
  · rintro ⟨s,hs⟩
    exact ⟨(projection p 0,s),(eq_X_of_direction p s hs).symm⟩
  · rintro ⟨q,rfl⟩
    exact ⟨q.2,rfl⟩

theorem chartYSet_eq_range : chartYSet = Set.range (fun q : ℂ × ℂ => Y q.1 q.2) := by
  ext p
  constructor
  · rintro ⟨s,hs⟩
    exact ⟨(projection p 1,s),(eq_Y_of_direction p s hs).symm⟩
  · rintro ⟨q,rfl⟩
    exact ⟨q.2,rfl⟩

theorem chart_sets_cover : chartXSet ∪ chartYSet = Set.univ := by
  ext p
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  exact direction_cover (direction p)

/-- An actual set equivalence between affine coordinates and the first chart domain. -/
noncomputable def chartX : (ℂ × ℂ) ≃ chartXSet :=
  (Equiv.ofInjective (fun q : ℂ × ℂ => X q.1 q.2) X_injective).trans
    (Equiv.setCongr chartXSet_eq_range.symm)

/-- An actual set equivalence between affine coordinates and the second chart domain. -/
noncomputable def chartY : (ℂ × ℂ) ≃ chartYSet :=
  (Equiv.ofInjective (fun q : ℂ × ℂ => Y q.1 q.2) Y_injective).trans
    (Equiv.setCongr chartYSet_eq_range.symm)

@[simp] theorem chartX_apply (q : ℂ × ℂ) : (chartX q).val = X q.1 q.2 := rfl
@[simp] theorem chartY_apply (q : ℂ × ℂ) : (chartY q).val = Y q.1 q.2 := rfl

@[simp] theorem projection_X_eq_zero_iff (r s : ℂ) : projection (X r s) = 0 ↔ r = 0 := by
  constructor
  · intro h
    simpa using congrFun h 0
  · intro h; subst r; ext i; fin_cases i <;> simp

@[simp] theorem projection_Y_eq_zero_iff (r s : ℂ) : projection (Y r s) = 0 ↔ r = 0 := by
  constructor
  · intro h
    simpa using congrFun h 1
  · intro h; subst r; ext i; fin_cases i <;> simp

/-- A projective line gives exactly one point of the exceptional fibre. -/
def exceptionalPoint (d : Direction) : Point := ⟨(0,d), d.submodule.zero_mem⟩

@[simp] theorem projection_exceptionalPoint (d : Direction) :
    projection (exceptionalPoint d) = 0 := rfl
@[simp] theorem direction_exceptionalPoint (d : Direction) :
    direction (exceptionalPoint d) = d := rfl

/-- The exceptional fibre is genuinely in bijection with the complex projective line. -/
def exceptionalEquiv : Direction ≃ {p : Point // projection p = 0} where
  toFun d := ⟨exceptionalPoint d,rfl⟩
  invFun p := direction p.val
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    exact point_ext p.property.symm rfl

theorem lineX_eq_lineY_inv (s : ℂ) (hs : s ≠ 0) : lineX s = lineY s⁻¹ := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨s, ?_⟩
  ext i; fin_cases i <;> simp [vectorX, vectorY, hs]

theorem X_eq_Y_transition (r s : ℂ) (hs : s ≠ 0) : X r s = Y (r*s) s⁻¹ := by
  apply point_ext
  · ext i; fin_cases i <;> simp [hs, mul_assoc]
  · exact lineX_eq_lineY_inv s hs

theorem Y_eq_X_transition (r s : ℂ) (hs : s ≠ 0) : Y r s = X (r*s) s⁻¹ := by
  have h := X_eq_Y_transition (r*s) s⁻¹ (inv_ne_zero hs)
  simpa [mul_assoc,hs] using h.symm

/-- The affine transition on the overlap has nonzero second coordinate. -/
def transition (q : ℂ × ℂ) : ℂ × ℂ := (q.1*q.2,q.2⁻¹)

theorem transition_involution (q : ℂ × ℂ) (hq : q.2 ≠ 0) :
    transition (transition q) = q := by
  apply Prod.ext <;> simp [transition,mul_assoc,hq]

theorem transition_differentiableAt (q : ℂ × ℂ) (hq : q.2 ≠ 0) :
    DifferentiableAt ℂ transition q := by
  exact (differentiableAt_fst.mul differentiableAt_snd).prodMk
    (differentiableAt_snd.inv hq)

/-- Exact homogeneous-coordinate criterion for the two projective affine charts. -/
theorem lineX_eq_lineY_iff (s t : ℂ) : lineX s = lineY t ↔ s*t = 1 := by
  constructor
  · intro h
    rcases (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h with ⟨a,ha⟩
    have h0 := congrFun ha 0
    have h1 := congrFun ha 1
    simp [vectorX,vectorY] at h0 h1
    simpa [h1] using h0
  · intro h
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    refine ⟨s,?_⟩
    ext i; fin_cases i <;> simp [vectorX,vectorY,h]

theorem X_eq_Y_iff (r s u v : ℂ) : X r s = Y u v ↔ u = r*s ∧ s*v = 1 := by
  constructor
  · intro h
    refine ⟨?_,(lineX_eq_lineY_iff s v).mp (congrArg direction h)⟩
    have h1 := congrArg (fun p => projection p 1) h
    simpa using h1.symm
  · rintro ⟨rfl,h⟩
    apply point_ext
    · ext i; fin_cases i <;> simp [mul_assoc,h]
    · exact (lineX_eq_lineY_iff s v).mpr h

@[simp] theorem X_mem_chartYSet_iff (r s : ℂ) : X r s ∈ chartYSet ↔ s ≠ 0 := by
  constructor
  · rintro ⟨t,ht⟩ hs
    have h := (lineX_eq_lineY_iff s t).mp ht
    simp [hs] at h
  · intro hs
    exact ⟨s⁻¹,lineX_eq_lineY_inv s hs⟩

@[simp] theorem Y_mem_chartXSet_iff (r s : ℂ) : Y r s ∈ chartXSet ↔ s ≠ 0 := by
  constructor
  · rintro ⟨t,ht⟩ hs
    have h := (lineX_eq_lineY_iff t s).mp ht.symm
    simp [hs] at h
  · intro hs
    refine ⟨s⁻¹,?_⟩
    simpa using (lineX_eq_lineY_inv s⁻¹ (inv_ne_zero hs)).symm

/-- The common coordinate domain of the transition maps. -/
def overlap : Set (ℂ × ℂ) := {q | q.2 ≠ 0}

/-- The transition is a bijection of its true overlap, with the same inverse formula. -/
def transitionEquiv : overlap ≃ overlap where
  toFun q := ⟨transition q.val,inv_ne_zero q.property⟩
  invFun q := ⟨transition q.val,inv_ne_zero q.property⟩
  left_inv q := Subtype.ext (transition_involution q.val q.property)
  right_inv q := Subtype.ext (transition_involution q.val q.property)

@[simp] theorem transitionEquiv_apply (q : overlap) :
    (transitionEquiv q).val = transition q.val := rfl

theorem overlap_isOpen : IsOpen overlap := by
  exact isOpen_ne.preimage continuous_snd

theorem transition_differentiableOn : DifferentiableOn ℂ transition overlap := by
  intro q hq
  exact (transition_differentiableAt q hq).differentiableWithinAt

theorem transition_continuousOn : ContinuousOn transition overlap :=
  transition_differentiableOn.continuousOn

end
end FailureOfSemipositiveMetricExtension.Blowup
