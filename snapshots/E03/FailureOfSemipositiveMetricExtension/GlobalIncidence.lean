import FailureOfSemipositiveMetricExtension.ProjectivePoints
import FailureOfSemipositiveMetricExtension.BlowupCharts
import FailureOfSemipositiveMetricExtension.ProjectivePlaneFamily

/-! The actual global four-centre incidence model, on mathlib projective quotient
points and four projective direction lines. It is defined over all complex t.
This file proves representative independence and identifies its four centres;
it does not yet assert a global analytic blow-up universal property. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence
noncomputable section
open FailureOfSemipositiveMetricExtension.Coordinates

abbrev PlanePoint := Projectivization ℂ (Fin 3 → ℂ)
abbrev Direction := Projectivization ℂ (Fin 2 → ℂ)

def centreVector : Fin 4 → ℂ → (Fin 3 → ℂ)
  | 0, _ => p₁
  | 1, _ => p₂
  | 2, t => p₃ t
  | 3, _ => p₄

def centre : Fin 4 → ℂ → PlanePoint
  | 0, _ => P₁
  | 1, _ => P₂
  | 2, t => P₃ t
  | 3, _ => P₄

theorem centreVector_nonzero (i : Fin 4) (t : ℂ) : centreVector i t ≠ 0 := by
  fin_cases i
  · exact p₁_nonzero
  · exact p₂_nonzero
  · exact p₃_nonzero t
  · exact p₄_nonzero

@[simp] theorem centre_mk (i : Fin 4) (t : ℂ) :
    Projectivization.mk ℂ (centreVector i t) (centreVector_nonzero i t) = centre i t := by
  fin_cases i <;> rfl

@[simp] theorem centre_eq_projectivePlane_centre (i : Fin 4) (t : ℂ) :
    centre i t = FailureOfSemipositiveMetricExtension.ProjectivePlane.centre i t := by
  fin_cases i <;> rfl

theorem centre_injective (t : ℂ) : Function.Injective (fun i => centre i t) := by
  simpa only [centre_eq_projectivePlane_centre] using
    FailureOfSemipositiveMetricExtension.ProjectivePlane.centres_pairwise_distinct t

/-- The pairs of homogeneous linear equations for the four centre ideals. -/
def pair (i : Fin 4) (t : ℂ) (v : Fin 3 → ℂ) : Fin 2 → ℂ :=
  match i with
  | 0 => ![v 1,v 2]
  | 1 => ![v 0,v 2]
  | 2 => ![v 1-v 0,v 2-t*v 0]
  | 3 => ![v 0,v 1]

def pairMap (i : Fin 4) (t : ℂ) : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun := pair i t
  map_add' v w := by ext j; fin_cases i <;> fin_cases j <;> simp [pair] <;> ring
  map_smul' a v := by ext j; fin_cases i <;> fin_cases j <;> simp [pair] <;> ring

@[simp] theorem pairMap_centre (i : Fin 4) (t : ℂ) :
    pairMap i t (centreVector i t) = 0 := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [pairMap,pair,centreVector,p₁,p₂,p₃,p₄]

/-- The zero vector is allowed: the entire kernel is exactly the centre line. -/
theorem pairMap_zero_iff_mem_centre (i : Fin 4) (t : ℂ) (v : Fin 3 → ℂ) :
    pairMap i t v = 0 ↔ v ∈ (centre i t).submodule := by
  rw [← centre_mk i t,Projectivization.submodule_mk,Submodule.mem_span_singleton]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    fin_cases i
    · refine ⟨v 0,?_⟩
      ext j; fin_cases j <;> simp [centreVector,p₁]
      · exact (show v 1 = 0 from h0).symm
      · exact (show v 2 = 0 from h1).symm
    · refine ⟨v 1,?_⟩
      ext j; fin_cases j <;> simp [centreVector,p₂]
      · exact (show v 0 = 0 from h0).symm
      · exact (show v 2 = 0 from h1).symm
    · refine ⟨v 0,?_⟩
      have hy : v 1 = v 0 := sub_eq_zero.mp h0
      have hz : v 2 = t*v 0 := sub_eq_zero.mp h1
      ext j; fin_cases j <;> simp [centreVector,p₃,hy,hz,mul_comm]
    · refine ⟨v 2,?_⟩
      ext j; fin_cases j <;> simp [centreVector,p₄]
      · exact (show v 0 = 0 from h0).symm
      · exact (show v 1 = 0 from h1).symm
  · rintro ⟨a,ha⟩
    rw [← ha,map_smul,pairMap_centre,smul_zero]

/-- Membership in a projective direction characterizes the projective class of a
nonzero vector, uniformly in the ambient vector-space dimension. -/
theorem projective_eq_iff_mem {n : ℕ} (v : Fin n → ℂ) (hv : v ≠ 0)
    (d : Projectivization ℂ (Fin n → ℂ)) :
    Projectivization.mk ℂ v hv = d ↔ v ∈ d.submodule := by
  rw [← Projectivization.mk_rep d,Projectivization.submodule_mk,Submodule.mem_span_singleton]
  exact Projectivization.mk_eq_mk_iff' ℂ _ _ _ _

theorem pairMap_rep_zero_iff (p : PlanePoint) (i : Fin 4) (t : ℂ) :
    pairMap i t p.rep = 0 ↔ p = centre i t := by
  rw [pairMap_zero_iff_mem_centre,← projective_eq_iff_mem p.rep p.rep_nonzero,
    Projectivization.mk_rep]

/-- A representative-independent incidence condition, expressed as submodule inclusion. -/
def Incidence (p : PlanePoint) (d : Direction) (i : Fin 4) (t : ℂ) : Prop :=
  p.submodule ≤ d.submodule.comap (pairMap i t)

/-- The quotient-level condition is equivalent to the expected equation for every
chosen nonzero representative, so no arbitrary choice of rep is hidden. -/
theorem incidence_mk_iff (v : Fin 3 → ℂ) (hv : v ≠ 0)
    (d : Direction) (i : Fin 4) (t : ℂ) :
    Incidence (Projectivization.mk ℂ v hv) d i t ↔ pairMap i t v ∈ d.submodule := by
  change (Projectivization.mk ℂ v hv).submodule ≤ _ ↔ _
  rw [Projectivization.submodule_mk,Submodule.span_singleton_le_iff_mem]
  rfl

theorem incidence_rep_iff (p : PlanePoint) (d : Direction) (i : Fin 4) (t : ℂ) :
    Incidence p d i t ↔ pairMap i t p.rep ∈ d.submodule := by
  conv_lhs => rw [← Projectivization.mk_rep p]
  exact incidence_mk_iff _ _ _ _ _

/-- Every direction is admissible above the corresponding centre. -/
theorem incidence_centre (i : Fin 4) (t : ℂ) (d : Direction) :
    Incidence (centre i t) d i t := by
  rw [← centre_mk i t,incidence_mk_iff,pairMap_centre]
  exact d.submodule.zero_mem

/-- Away from a centre the incidence condition forces the unique projective direction. -/
theorem incidence_unique_away (p : PlanePoint) (i : Fin 4) (t : ℂ)
    (hp : p ≠ centre i t) (d : Direction) :
    Incidence p d i t ↔
      d = Projectivization.mk ℂ (pairMap i t p.rep)
        (fun hz => hp ((pairMap_rep_zero_iff p i t).mp hz)) := by
  rw [incidence_rep_iff,← projective_eq_iff_mem]
  exact eq_comm

/-- A canonical choice is used only to exhibit a point, not to define incidence. -/
def chosenDirection (p : PlanePoint) (i : Fin 4) (t : ℂ) : Direction :=
  if h : pairMap i t p.rep = 0 then FailureOfSemipositiveMetricExtension.Blowup.lineX 0
  else Projectivization.mk ℂ (pairMap i t p.rep) h

theorem chosenDirection_incidence (p : PlanePoint) (i : Fin 4) (t : ℂ) :
    Incidence p (chosenDirection p i t) i t := by
  rw [incidence_rep_iff]
  unfold chosenDirection
  split_ifs with h
  · rw [h]; exact Submodule.zero_mem _
  · rw [Projectivization.submodule_mk]
    exact Submodule.mem_span_singleton_self _

/-- The global incidence total space; the four simultaneous conditions are imposed
on actual projective points and direction lines. -/
def Total := {q : PlanePoint × (Fin 4 → Direction) × ℂ //
  ∀ i, Incidence q.1 (q.2.1 i) i q.2.2}

def projection (q : Total) : ℂ := q.val.2.2
def blowdown (q : Total) : PlanePoint := q.val.1
def directions (q : Total) : Fin 4 → Direction := q.val.2.1

def Fiber (t : ℂ) := {q : PlanePoint × (Fin 4 → Direction) //
  ∀ i, Incidence q.1 (q.2 i) i t}

@[ext] theorem total_ext {p q : Total} (hb : blowdown p = blowdown q)
    (hd : directions p = directions q) (ht : projection p = projection q) : p = q :=
  Subtype.ext (Prod.ext hb (Prod.ext hd ht))

/-- The simultaneous incidence model has a point over every projective point in every fibre. -/
theorem blowdown_projection_surjective : Function.Surjective (fun q : Total => (blowdown q,projection q)) := by
  rintro ⟨p,t⟩
  exact ⟨⟨(p,(fun i => chosenDirection p i t),t),fun i => chosenDirection_incidence p i t⟩,rfl⟩

/-- Outside the union of the four centres, the global incidence point over (p,t) is unique. -/
theorem unique_away_from_centres (q q' : Total)
    (hb : blowdown q = blowdown q') (ht : projection q = projection q')
    (haway : ∀ i, blowdown q ≠ centre i (projection q)) : q = q' := by
  apply total_ext hb _ ht
  funext i
  have hd := (incidence_unique_away (blowdown q) i (projection q) (haway i) (directions q i)).mp (q.property i)
  have hq' : Incidence (blowdown q) (directions q' i) i (projection q) := by
    rw [hb,ht]; exact q'.property i
  exact hd.trans ((incidence_unique_away (blowdown q) i (projection q) (haway i) (directions q' i)).mp hq').symm

/-- A point above the i-th centre with an arbitrary i-th exceptional direction. -/
def pointOverCentre (i : Fin 4) (t : ℂ) (d : Direction) : Total :=
  ⟨(centre i t,(fun j => if j = i then d else chosenDirection (centre i t) j t),t),by
    intro j
    dsimp
    split_ifs with h
    · subst j; exact incidence_centre i t d
    · exact chosenDirection_incidence (centre i t) j t⟩

@[simp] theorem pointOverCentre_blowdown (i : Fin 4) (t : ℂ) (d : Direction) :
    blowdown (pointOverCentre i t d) = centre i t := rfl

@[simp] theorem pointOverCentre_projection (i : Fin 4) (t : ℂ) (d : Direction) :
    projection (pointOverCentre i t d) = t := rfl

@[simp] theorem pointOverCentre_direction (i : Fin 4) (t : ℂ) (d : Direction) :
    directions (pointOverCentre i t d) i = d := by simp [directions,pointOverCentre]

theorem directions_eq_away (q q' : Total) (j : Fin 4)
    (hb : blowdown q = blowdown q') (ht : projection q = projection q')
    (haway : blowdown q ≠ centre j (projection q)) : directions q j = directions q' j := by
  have hq := (incidence_unique_away (blowdown q) j (projection q) haway (directions q j)).mp (q.property j)
  have hq' : Incidence (blowdown q) (directions q' j) j (projection q) := by
    rw [hb,ht]; exact q'.property j
  exact hq.trans ((incidence_unique_away (blowdown q) j (projection q) haway (directions q' j)).mp hq').symm

/-- The set-theoretic exceptional fibre at each specified centre is the actual P¹. -/
def exceptionalFiberEquiv (i : Fin 4) (t : ℂ) :
    {q : Total // blowdown q = centre i t ∧ projection q = t} ≃ Direction where
  toFun q := directions q.val i
  invFun d := ⟨pointOverCentre i t d,⟨rfl,rfl⟩⟩
  left_inv q := by
    apply Subtype.ext
    change pointOverCentre i t (directions q.val i) = q.val
    apply total_ext (p := pointOverCentre i t (directions q.val i)) (q := q.val)
      q.property.1.symm _ q.property.2.symm
    funext j
    by_cases hj : j = i
    · subst j; simp
    · apply directions_eq_away (pointOverCentre i t (directions q.val i)) q.val j
        q.property.1.symm q.property.2.symm
      change centre i t ≠ centre j t
      exact (centre_injective t).ne (Ne.symm hj)
  right_inv d := pointOverCentre_direction i t d

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence
