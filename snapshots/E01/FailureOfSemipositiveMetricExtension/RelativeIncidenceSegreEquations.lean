import FailureOfSemipositiveMetricExtension.RelativeSegreEquations

/-! The four bihomogeneous incidence equations become thirty-two linear
homogeneous equations after the genuine Segre embedding into projective 47-space.
Together with the explicit Segre equations they characterize the original total
space exactly on complex points. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.RelativeSegre
noncomputable section
open Set MvPolynomial

abbrev MissingIndex := Fin 3 → Fin 2

def insertedVariable (r : Fin 4) (k : MissingIndex) (a : Fin 3) (b : Fin 2) : PolynomialRing :=
  X (a,Fin.insertNth r b k)

def incidencePolynomial : Fin 4 → MissingIndex → PolynomialRing
  | 0,k => insertedVariable 0 k 1 1 - insertedVariable 0 k 2 0
  | 1,k => insertedVariable 1 k 0 1 - insertedVariable 1 k 2 0
  | 2,k => insertedVariable 2 k 1 1 - insertedVariable 2 k 0 1 -
      insertedVariable 2 k 2 0 + C Polynomial.X * insertedVariable 2 k 0 0
  | 3,k => insertedVariable 3 k 0 1 - insertedVariable 3 k 1 0

theorem incidencePolynomial_homogeneous (r : Fin 4) (k : MissingIndex) :
    IsHomogeneous (incidencePolynomial r k) 1 := by
  have h (r : Fin 4) (a : Fin 3) (b : Fin 2) : IsHomogeneous (insertedVariable r k a b) 1 :=
    isHomogeneous_X Coefficient _
  have hT : IsHomogeneous (C Polynomial.X * insertedVariable 2 k 0 0) 1 := by
    simpa using (isHomogeneous_C Index (Polynomial.X : Coefficient)).mul (h 2 0 0)
  fin_cases r
  · exact (h 0 1 1).sub (h 0 2 0)
  · exact (h 1 0 1).sub (h 1 2 0)
  · exact (((h 2 1 1).sub (h 2 0 1)).sub (h 2 2 0)).add hT
  · exact (h 3 0 1).sub (h 3 1 0)

def missingProduct (r : Fin 4) (k : MissingIndex) (w : Fin 4 → Fin 2 → ℂ) : ℂ :=
  ∏ j : Fin 3, w (r.succAbove j) (k j)

theorem tensorVector_insertNth (v : Fin 3 → ℂ) (w : Fin 4 → Fin 2 → ℂ)
    (r : Fin 4) (k : MissingIndex) (a : Fin 3) (b : Fin 2) :
    tensorVector v w (a,Fin.insertNth r b k) = v a * w r b * missingProduct r k w := by
  simp only [tensorVector]
  rw [Fin.prod_univ_succAbove _ r]
  simp [missingProduct,mul_assoc]

theorem evaluate_incidencePolynomial_tensorVector (t : ℂ)
    (v : Fin 3 → ℂ) (w : Fin 4 → Fin 2 → ℂ) (r : Fin 4) (k : MissingIndex) :
    evaluate t (tensorVector v w) (incidencePolynomial r k) =
      IncidenceEquations.evaluate t v w (IncidenceEquations.equation r) * missingProduct r k w := by
  rw [IncidenceEquations.evaluate_equation]
  fin_cases r <;>
    simp only [incidencePolynomial,evaluate,insertedVariable,eval₂_sub,eval₂_add,eval₂_mul,
      eval₂_X,eval₂_C,Polynomial.coe_evalRingHom,Polynomial.eval_X,tensorVector_insertNth]
  all_goals norm_num only [Fin.reduceFinMk] at *
  all_goals simp only [pairMap,pair,LinearMap.coe_mk,AddHom.coe_mk,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.head_cons,Matrix.tail_cons,Matrix.cons_val_two] <;> ring!

theorem exists_missingProduct_ne_zero (r : Fin 4) (w : Fin 4 → Fin 2 → ℂ)
    (hw : ∀ r, w r ≠ 0) : ∃ k, missingProduct r k w ≠ 0 := by
  have h : ∀ j : Fin 3, ∃ e, w (r.succAbove j) e ≠ 0 := by
    intro j
    contrapose! hw
    exact ⟨r.succAbove j,funext hw⟩
  choose k hk using h
  exact ⟨k,Finset.prod_ne_zero_iff.mpr (fun j _ => hk j)⟩

/-- Exact equivalence between the 32 Segre-linear equations and the original four equations. -/
theorem incidencePolynomials_zero_iff (t : ℂ) (v : Fin 3 → ℂ)
    (w : Fin 4 → Fin 2 → ℂ) (hw : ∀ r, w r ≠ 0) :
    (∀ r k, evaluate t (tensorVector v w) (incidencePolynomial r k) = 0) ↔
      ∀ r, IncidenceEquations.evaluate t v w (IncidenceEquations.equation r) = 0 := by
  constructor
  · intro h r
    obtain ⟨k,hk⟩ := exists_missingProduct_ne_zero r w hw
    exact (mul_eq_zero.mp ((evaluate_incidencePolynomial_tensorVector t v w r k).symm.trans
      (h r k))).resolve_right hk
  · intro h r k
    rw [evaluate_incidencePolynomial_tensorVector,h r,zero_mul]

/-- The original total space mapped into the actual projective Segre target, with its parameter. -/
def relativePoint (p : Total) : Point × ℂ := (point (blowdown p,directions p),projection p)

theorem relativePoint_injective : Function.Injective relativePoint := by
  intro p q h
  have hp := point_injective (congrArg Prod.fst h)
  apply total_ext
  · exact congrArg (fun x : Product => x.1) hp
  · exact congrArg (fun x : Product => x.2) hp
  · exact congrArg (fun x : Point × ℂ => x.2) h

theorem relativePoint_tensor_mem_range_iff (t : ℂ) (v : Fin 3 → ℂ) (hv : v ≠ 0)
    (w : Fin 4 → Fin 2 → ℂ) (hw : ∀ r, w r ≠ 0) :
    (Projectivization.mk ℂ (tensorVector v w) (tensorVector_nonzero v hv w hw),t) ∈
      range relativePoint ↔ ∀ r, IncidenceEquations.evaluate t v w (IncidenceEquations.equation r) = 0 := by
  let q : Product := (Projectivization.mk ℂ v hv,fun r => Projectivization.mk ℂ (w r) (hw r))
  have hq : point q = Projectivization.mk ℂ (tensorVector v w) (tensorVector_nonzero v hv w hw) :=
    point_mk v hv w hw
  constructor
  · rintro ⟨p,hp⟩
    have hprod : (blowdown p,directions p) = q := point_injective ((congrArg Prod.fst hp).trans hq.symm)
    have ht : projection p = t := congrArg Prod.snd hp
    apply (IncidenceEquations.totalLocus_iff_equations t v hv w hw).mp
    have hh := p.property
    change ∀ r, Incidence (blowdown p) (directions p r) r (projection p) at hh
    change ∀ r, Incidence q.1 (q.2 r) r t
    rw [← congrArg Prod.fst hprod,← congrArg Prod.snd hprod,← ht]
    exact hh
  · intro h
    exact ⟨⟨(q.1,q.2,t),(IncidenceEquations.totalLocus_iff_equations t v hv w hw).mpr h⟩,
      Prod.ext hq rfl⟩

/-- The complete relative homogeneous presentation agrees with the existing total space
on every nonzero complex homogeneous vector and every parameter. -/
theorem mk_mem_range_relativePoint_iff (t : ℂ) (z : Vector) (hz : z ≠ 0) :
    (Projectivization.mk ℂ z hz,t) ∈ range relativePoint ↔
      (∀ p i, evaluate t z (pivotPolynomial p i) = 0) ∧
      (∀ r k, evaluate t z (incidencePolynomial r k) = 0) := by
  constructor
  · rintro ⟨q,hq⟩
    have hseg : Projectivization.mk ℂ z hz ∈ range point :=
      ⟨(blowdown q,directions q),congrArg Prod.fst hq⟩
    have hp := (mk_mem_range_point_iff t z hz).mp hseg
    refine ⟨hp,?_⟩
    obtain ⟨v,hv,w,hw,hz'⟩ := (exists_tensorVector_iff t z hz).mpr hp
    have hr : (Projectivization.mk ℂ (tensorVector v w) (tensorVector_nonzero v hv w hw),t) ∈
        range relativePoint := by simpa only [hz'] using (show (Projectivization.mk ℂ z hz,t) ∈ range relativePoint from ⟨q,hq⟩)
    have he := (relativePoint_tensor_mem_range_iff t v hv w hw).mp hr
    simpa only [hz'] using (incidencePolynomials_zero_iff t v w hw).mpr he
  · rintro ⟨hp,hi⟩
    obtain ⟨v,hv,w,hw,hz'⟩ := (exists_tensorVector_iff t z hz).mpr hp
    have he := (incidencePolynomials_zero_iff t v w hw).mp (by simpa only [hz'] using hi)
    simpa only [hz'] using (relativePoint_tensor_mem_range_iff t v hv w hw).mpr he

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.RelativeSegre
