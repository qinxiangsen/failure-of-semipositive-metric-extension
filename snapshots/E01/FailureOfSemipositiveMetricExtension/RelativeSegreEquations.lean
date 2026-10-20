import FailureOfSemipositiveMetricExtension.RelativeSegreCoordinates
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Explicit homogeneous equations cutting out the Segre image on all nonzero
vectors. We use degree-five pivot identities to obtain a direct reconstruction
proof, rather than presupposing the usual quadratic ideal theorem. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.RelativeSegre
noncomputable section
open Set MvPolynomial

abbrev Coefficient := Polynomial ℂ
abbrev PolynomialRing := MvPolynomial Index Coefficient

def baseIndex (p i : Index) : Index := (i.1,p.2)
def directionIndex (p i : Index) (r : Fin 4) : Index := (p.1,Function.update p.2 r (i.2 r))

def pivotPolynomial (p i : Index) : PolynomialRing :=
  X i * X p ^ 4 - X (baseIndex p i) * ∏ r, X (directionIndex p i r)

def evaluate (t : ℂ) (z : Vector) (f : PolynomialRing) : ℂ :=
  eval₂ (Polynomial.evalRingHom t) z f

@[simp] theorem evaluate_pivotPolynomial (t : ℂ) (z : Vector) (p i : Index) :
    evaluate t z (pivotPolynomial p i) =
      z i * z p ^ 4 - z (baseIndex p i) * ∏ r, z (directionIndex p i r) := by
  simp [evaluate,pivotPolynomial]

theorem pivotPolynomial_homogeneous (p i : Index) : IsHomogeneous (pivotPolynomial p i) 5 := by
  apply IsHomogeneous.sub
  · simpa using (isHomogeneous_X (R := Coefficient) i).mul
      ((isHomogeneous_X (R := Coefficient) p).pow 4)
  · have hp : IsHomogeneous (∏ r : Fin 4, (X (directionIndex p i r) : PolynomialRing)) 4 := by
      simpa using IsHomogeneous.prod Finset.univ (fun r : Fin 4 => (X (directionIndex p i r) : PolynomialRing))
        (fun _ => 1) (fun r _ => isHomogeneous_X Coefficient _)
    simpa using (isHomogeneous_X (R := Coefficient) (baseIndex p i)).mul hp

/-- Every actual pure tensor satisfies the homogeneous pivot equations. -/
theorem tensorVector_pivot_identity (v : Fin 3 → ℂ) (w : Fin 4 → Fin 2 → ℂ) (p i : Index) :
    tensorVector v w i * tensorVector v w p ^ 4 =
      tensorVector v w (baseIndex p i) * ∏ r, tensorVector v w (directionIndex p i r) := by
  simp [tensorVector,baseIndex,directionIndex,Fin.prod_univ_succ]
  ring

@[simp] theorem evaluate_pivotPolynomial_tensorVector (t : ℂ)
    (v : Fin 3 → ℂ) (w : Fin 4 → Fin 2 → ℂ) (p i : Index) :
    evaluate t (tensorVector v w) (pivotPolynomial p i) = 0 := by
  rw [evaluate_pivotPolynomial,tensorVector_pivot_identity,sub_self]

def recoveredBase (p : Index) (z : Vector) : Fin 3 → ℂ := baseSlice p.2 z

def recoveredDirections (p : Index) (z : Vector) : Fin 4 → Fin 2 → ℂ :=
  fun r e => directionSlice p r z e / z p

theorem recoveredBase_nonzero (p : Index) (z : Vector) (hp : z p ≠ 0) : recoveredBase p z ≠ 0 := by
  intro hz
  exact hp (congrFun hz p.1)

theorem recoveredDirections_nonzero (p : Index) (z : Vector) (hp : z p ≠ 0) (r : Fin 4) :
    recoveredDirections p z r ≠ 0 := by
  intro hz
  have h := congrFun hz (p.2 r)
  simp [recoveredDirections,directionSlice,hp] at h

/-- A single nonzero pivot and its equations explicitly recover all five factors. -/
theorem tensorVector_reconstruction (t : ℂ) (p : Index) (z : Vector) (hp : z p ≠ 0)
    (h : ∀ i, evaluate t z (pivotPolynomial p i) = 0) :
    tensorVector (recoveredBase p z) (recoveredDirections p z) = z := by
  ext i
  have hi := sub_eq_zero.mp ((evaluate_pivotPolynomial t z p i).symm.trans (h i))
  simp only [tensorVector,recoveredBase,baseSlice,recoveredDirections,directionSlice]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [← mul_div_assoc]
  exact (div_eq_iff (pow_ne_zero 4 hp)).mpr hi.symm

/-- Exact global affine-cone zero-locus characterization, including all pivots. -/
theorem exists_tensorVector_iff (t : ℂ) (z : Vector) (hz : z ≠ 0) :
    (∃ (v : Fin 3 → ℂ) (_ : v ≠ 0) (w : Fin 4 → Fin 2 → ℂ) (_ : ∀ r, w r ≠ 0),
      tensorVector v w = z) ↔ ∀ p i, evaluate t z (pivotPolynomial p i) = 0 := by
  constructor
  · rintro ⟨v,hv,w,hw,rfl⟩ p i
    exact evaluate_pivotPolynomial_tensorVector t v w p i
  · intro h
    have hex : ∃ p, z p ≠ 0 := by contrapose! hz; exact funext hz
    obtain ⟨p,hp⟩ := hex
    exact ⟨recoveredBase p z,recoveredBase_nonzero p z hp,recoveredDirections p z,
      recoveredDirections_nonzero p z hp,tensorVector_reconstruction t p z hp (h p)⟩

/-- The genuine projective Segre image is exactly the specified homogeneous zero locus. -/
theorem mk_mem_range_point_iff (t : ℂ) (z : Vector) (hz : z ≠ 0) :
    Projectivization.mk ℂ z hz ∈ range point ↔ ∀ p i, evaluate t z (pivotPolynomial p i) = 0 := by
  constructor
  · rintro ⟨q,hq⟩
    obtain ⟨c,hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp hq.symm
    have hc0 : c ≠ 0 := by
      intro hc0
      rw [hc0,zero_smul] at hc
      exact hz hc.symm
    apply (exists_tensorVector_iff t z hz).mp
    refine ⟨c • q.1.rep,smul_ne_zero hc0 q.1.rep_nonzero,
      (fun r => (q.2 r).rep),(fun r => (q.2 r).rep_nonzero),?_⟩
    have hs := tensorVector_rescale c (fun _ => 1) q.1.rep (fun r => (q.2 r).rep)
    simp only [Finset.prod_const_one,mul_one,one_smul] at hs
    exact hs.trans hc
  · intro h
    obtain ⟨v,hv,w,hw,hz'⟩ := (exists_tensorVector_iff t z hz).mpr h
    refine ⟨(Projectivization.mk ℂ v hv,fun r => Projectivization.mk ℂ (w r) (hw r)),?_⟩
    rw [point_mk]
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    exact ⟨1,by simpa only [one_smul] using hz'.symm⟩

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.RelativeSegre
