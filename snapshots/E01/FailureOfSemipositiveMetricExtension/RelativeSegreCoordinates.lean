import FailureOfSemipositiveMetricExtension.GlobalBlowdownAffineSchemes

/-! Actual Segre coordinates for the original product of one projective plane
and four projective lines. This file is algebraic and installs no topology on
the target projectivization. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.RelativeSegre
noncomputable section
open Set

abbrev Index := Fin 3 × (Fin 4 → Fin 2)
abbrev Vector := Index → ℂ
abbrev Point := Projectivization ℂ Vector
abbrev Product := PlanePoint × (Fin 4 → Direction)

def tensorVector (v : Fin 3 → ℂ) (w : Fin 4 → Fin 2 → ℂ) : Vector :=
  fun i => v i.1 * ∏ r, w r (i.2 r)

theorem index_card : Fintype.card Index = 48 := by simp [Index]

theorem tensorVector_nonzero (v : Fin 3 → ℂ) (hv : v ≠ 0)
    (w : Fin 4 → Fin 2 → ℂ) (hw : ∀ r, w r ≠ 0) : tensorVector v w ≠ 0 := by
  have hx : ∃ a, v a ≠ 0 := by contrapose! hv; exact funext hv
  have hy : ∀ r, ∃ e, w r e ≠ 0 := by
    intro r
    by_contra h
    push_neg at h
    exact hw r (funext h)
  obtain ⟨a,ha⟩ := hx
  choose e he using hy
  intro h
  exact (mul_ne_zero ha (Finset.prod_ne_zero_iff.mpr (fun r _ => he r))) (congrFun h (a,e))

theorem tensorVector_rescale (c : ℂ) (d : Fin 4 → ℂ)
    (v : Fin 3 → ℂ) (w : Fin 4 → Fin 2 → ℂ) :
    tensorVector (c • v) (fun r => d r • w r) = (c * ∏ r, d r) • tensorVector v w := by
  ext i
  simp only [tensorVector,Pi.smul_apply,smul_eq_mul,Finset.prod_mul_distrib]
  ring

def point (p : Product) : Point :=
  Projectivization.mk ℂ (tensorVector p.1.rep (fun r => (p.2 r).rep))
    (tensorVector_nonzero _ p.1.rep_nonzero _ (fun r => (p.2 r).rep_nonzero))

/-- Exact descent from arbitrary nonzero homogeneous coordinates. -/
theorem point_mk (v : Fin 3 → ℂ) (hv : v ≠ 0)
    (w : Fin 4 → Fin 2 → ℂ) (hw : ∀ r, w r ≠ 0) :
    point (Projectivization.mk ℂ v hv,fun r => Projectivization.mk ℂ (w r) (hw r)) =
      Projectivization.mk ℂ (tensorVector v w) (tensorVector_nonzero v hv w hw) := by
  obtain ⟨c,hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  choose d hd using (fun r => Projectivization.exists_smul_eq_mk_rep ℂ (w r) (hw r))
  have hcv : (Projectivization.mk ℂ v hv).rep = (c : ℂ) • v := hc.symm
  have hdv : (fun r => (Projectivization.mk ℂ (w r) (hw r)).rep) =
      (fun r => (d r : ℂ) • w r) := funext (fun r => (hd r).symm)
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨(c : ℂ) * ∏ r, (d r : ℂ),?_⟩
  change _ = tensorVector (Projectivization.mk ℂ v hv).rep
    (fun r => (Projectivization.mk ℂ (w r) (hw r)).rep)
  rw [hcv,hdv,tensorVector_rescale]

def baseSlice (k : Fin 4 → Fin 2) (z : Vector) : Fin 3 → ℂ := fun a => z (a,k)

def directionSlice (i : Index) (r : Fin 4) (z : Vector) : Fin 2 → ℂ :=
  fun e => z (i.1,Function.update i.2 r e)

@[simp] theorem baseSlice_tensorVector (k : Fin 4 → Fin 2)
    (v : Fin 3 → ℂ) (w : Fin 4 → Fin 2 → ℂ) :
    baseSlice k (tensorVector v w) = (∏ r, w r (k r)) • v := by
  ext a
  simp [baseSlice,tensorVector,smul_eq_mul,mul_comm]

@[simp] theorem directionSlice_tensorVector (i : Index) (r : Fin 4)
    (v : Fin 3 → ℂ) (w : Fin 4 → Fin 2 → ℂ) :
    directionSlice i r (tensorVector v w) =
      (v i.1 * ∏ j ∈ Finset.univ.erase r, w j (i.2 j)) • w r := by
  classical
  ext e
  have hprod : (∏ j, w j (Function.update i.2 r e j)) =
      w r e * ∏ j ∈ Finset.univ.erase r, w j (i.2 j) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ r)]
    simp only [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    exact congrArg (w j) (Function.update_of_ne (Finset.mem_erase.mp hj).1 e i.2)
  simp only [directionSlice,tensorVector,hprod,Pi.smul_apply,smul_eq_mul]
  ring

theorem baseSlice_smul (k : Fin 4 → Fin 2) (c : ℂ) (z : Vector) :
    baseSlice k (c • z) = c • baseSlice k z := rfl

theorem directionSlice_smul (i : Index) (r : Fin 4) (c : ℂ) (z : Vector) :
    directionSlice i r (c • z) = c • directionSlice i r z := rfl

private theorem projective_eq_of_slices {ι : Type*} (v v' : ι → ℂ) (hv : v ≠ 0) (hv' : v' ≠ 0)
    (c c' a : ℂ) (hc : c ≠ 0) (h : c • v = a • (c' • v')) :
    Projectivization.mk ℂ v hv = Projectivization.mk ℂ v' hv' := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨c⁻¹ * (a*c'),?_⟩
  have hh := congrArg (fun z => c⁻¹ • z) h
  simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using hh.symm

/-- A nonzero tensor pivot reconstructs every original projective factor. -/
theorem point_injective : Function.Injective point := by
  intro p p' h
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
  have hn := tensorVector_nonzero _ p.1.rep_nonzero _ (fun r => (p.2 r).rep_nonzero)
  have hi : ∃ i, tensorVector p.1.rep (fun r => (p.2 r).rep) i ≠ 0 := by
    contrapose! hn
    exact funext hn
  obtain ⟨i,hi⟩ := hi
  have hbase : p.1.rep i.1 ≠ 0 := (mul_ne_zero_iff.mp hi).1
  have hdirs : ∀ r, (p.2 r).rep (i.2 r) ≠ 0 := by
    have hp : (∏ r, (p.2 r).rep (i.2 r)) ≠ 0 := (mul_ne_zero_iff.mp hi).2
    exact fun r => Finset.prod_ne_zero_iff.mp hp r (Finset.mem_univ r)
  apply Prod.ext
  · have hs := congrArg (baseSlice i.2) ha
    simp only [baseSlice_smul,baseSlice_tensorVector] at hs
    have hp := projective_eq_of_slices p.1.rep p'.1.rep p.1.rep_nonzero p'.1.rep_nonzero
      _ _ a (Finset.prod_ne_zero_iff.mpr (fun r _ => hdirs r)) hs.symm
    simpa only [Projectivization.mk_rep] using hp
  · funext r
    have hs := congrArg (directionSlice i r) ha
    simp only [directionSlice_smul,directionSlice_tensorVector] at hs
    have hp := projective_eq_of_slices (p.2 r).rep (p'.2 r).rep (p.2 r).rep_nonzero (p'.2 r).rep_nonzero
      _ _ a (mul_ne_zero hbase (Finset.prod_ne_zero_iff.mpr (fun j _ => hdirs j))) hs.symm
    simpa only [Projectivization.mk_rep] using hp

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.RelativeSegre
