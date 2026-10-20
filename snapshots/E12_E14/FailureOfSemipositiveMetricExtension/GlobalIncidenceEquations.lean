import FailureOfSemipositiveMetricExtension.GlobalBlowdownComplement
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! A concrete relative multi-projective presentation of the original incidence
set.  Its four equations are actual multivariate polynomials over `ℂ[T]`, with
mathlib weighted homogeneity in all five projective blocks.  This is an exact
presentation of the existing complex points, not a claimed scheme comparison. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.IncidenceEquations
noncomputable section
open Set MvPolynomial

abbrev Variable := Fin 3 ⊕ (Fin 4 × Fin 2)
abbrev Coefficient := Polynomial ℂ
abbrev Equation := MvPolynomial Variable Coefficient
abbrev MultiDegree := ℕ × (Fin 4 → ℕ)

def baseVariable (a : Fin 3) : Equation := X (Sum.inl a)
def directionVariable (r : Fin 4) (e : Fin 2) : Equation := X (Sum.inr (r,e))

def linearPair : Fin 4 → Fin 2 → Equation
  | 0, 0 => baseVariable 1
  | 0, 1 => baseVariable 2
  | 1, 0 => baseVariable 0
  | 1, 1 => baseVariable 2
  | 2, 0 => baseVariable 1 - baseVariable 0
  | 2, 1 => baseVariable 2 - C Polynomial.X * baseVariable 0
  | 3, 0 => baseVariable 0
  | 3, 1 => baseVariable 1

/-- The four relative equations: `y b₀-z a₀`, `x b₁-z a₁`,
`(y-x)b₂-(z-Tx)a₂`, and `x b₃-y a₃`. -/
def equation (r : Fin 4) : Equation :=
  linearPair r 0 * directionVariable r 1 - linearPair r 1 * directionVariable r 0

def weight : Variable → MultiDegree
  | Sum.inl _ => (1,0)
  | Sum.inr (r,_) => (0,Pi.single r 1)

def multidegree (r : Fin 4) : MultiDegree := (1,Pi.single r 1)

private theorem homogeneous_sub {p q : Equation} {d : MultiDegree}
    (hp : IsWeightedHomogeneous weight p d) (hq : IsWeightedHomogeneous weight q d) :
    IsWeightedHomogeneous weight (p-q) d :=
  (weightedHomogeneousSubmodule Coefficient weight d).sub_mem hp hq

theorem baseVariable_homogeneous (a : Fin 3) :
    IsWeightedHomogeneous weight (baseVariable a) (1,0) :=
  isWeightedHomogeneous_X Coefficient weight (Sum.inl a)

theorem directionVariable_homogeneous (r : Fin 4) (e : Fin 2) :
    IsWeightedHomogeneous weight (directionVariable r e) (0,Pi.single r 1) :=
  isWeightedHomogeneous_X Coefficient weight (Sum.inr (r,e))

theorem linearPair_homogeneous (r : Fin 4) (e : Fin 2) :
    IsWeightedHomogeneous weight (linearPair r e) (1,0) := by
  have hT : IsWeightedHomogeneous weight (C Polynomial.X * baseVariable 0) (1,0) := by
    simpa using (isWeightedHomogeneous_C weight (Polynomial.X : Coefficient)).mul
      (baseVariable_homogeneous 0)
  fin_cases r <;> fin_cases e
  all_goals first | exact baseVariable_homogeneous _ |
    exact homogeneous_sub (baseVariable_homogeneous _) (baseVariable_homogeneous _) |
    exact homogeneous_sub (baseVariable_homogeneous _) hT

/-- Each equation has degree one in the plane block, one in its own direction
block, and zero in the other three direction blocks. The parameter has degree zero. -/
theorem equation_multihomogeneous (r : Fin 4) :
    IsWeightedHomogeneous weight (equation r) (multidegree r) := by
  apply homogeneous_sub
  · simpa [multidegree] using (linearPair_homogeneous r 0).mul (directionVariable_homogeneous r 1)
  · simpa [multidegree] using (linearPair_homogeneous r 1).mul (directionVariable_homogeneous r 0)

def values (v : Fin 3 → ℂ) (w : Fin 4 → Fin 2 → ℂ) : Variable → ℂ := Sum.elim v (fun q => w q.1 q.2)

def evaluate (t : ℂ) (v : Fin 3 → ℂ) (w : Fin 4 → Fin 2 → ℂ) (f : Equation) : ℂ :=
  eval₂ (Polynomial.evalRingHom t) (values v w) f

@[simp] theorem evaluate_linearPair (t : ℂ) (v : Fin 3 → ℂ) (w : Fin 4 → Fin 2 → ℂ)
    (r : Fin 4) (e : Fin 2) : evaluate t v w (linearPair r e) = pairMap r t v e := by
  fin_cases r <;> fin_cases e <;>
    simp [evaluate,linearPair,baseVariable,values,pairMap,pair]

@[simp] theorem evaluate_equation (t : ℂ) (v : Fin 3 → ℂ) (w : Fin 4 → Fin 2 → ℂ)
    (r : Fin 4) : evaluate t v w (equation r) =
      pairMap r t v 0 * w r 1 - pairMap r t v 1 * w r 0 := by
  simp only [evaluate,equation,eval₂_sub,eval₂_mul,directionVariable,eval₂_X]
  change evaluate t v w (linearPair r 0) * w r 1 - evaluate t v w (linearPair r 1) * w r 0 = _
  rw [evaluate_linearPair,evaluate_linearPair]

/-- Incidence with an arbitrary nonzero homogeneous two-vector is exactly the
vanishing of its actual two-by-two determinant. -/
theorem mem_projectiveLine_iff_determinant (u v : Fin 2 → ℂ) (hv : v ≠ 0) :
    u ∈ (Projectivization.mk ℂ v hv).submodule ↔ u 0 * v 1 - u 1 * v 0 = 0 := by
  rw [Projectivization.submodule_mk,Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a,ha⟩
    rw [← ha]
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  · intro h
    by_cases h0 : v 0 = 0
    · have h1 : v 1 ≠ 0 := by
        intro h1
        apply hv
        ext i
        fin_cases i <;> assumption
      have hu : u 0 = 0 := by
        simpa [h0,h1] using h
      refine ⟨u 1 / v 1,?_⟩
      ext i
      fin_cases i <;> simp [h0,hu,h1,smul_eq_mul]
    · refine ⟨u 0 / v 0,?_⟩
      ext i
      fin_cases i
      · simp [smul_eq_mul,h0]
      · simp only [Pi.smul_apply,smul_eq_mul]
        apply (div_mul_eq_mul_div _ _ _).trans
        exact (div_eq_iff h0).mpr (sub_eq_zero.mp h)

/-- This iff holds for every choice of nonzero homogeneous representatives. -/
theorem incidence_iff_equation (t : ℂ) (v : Fin 3 → ℂ) (hv : v ≠ 0)
    (w : Fin 4 → Fin 2 → ℂ) (hw : ∀ r, w r ≠ 0) (r : Fin 4) :
    Incidence (Projectivization.mk ℂ v hv) (Projectivization.mk ℂ (w r) (hw r)) r t ↔
      evaluate t v w (equation r) = 0 := by
  rw [incidence_mk_iff,mem_projectiveLine_iff_determinant,evaluate_equation]

/-- Exact equality with the existing total-space incidence predicate. -/
theorem totalLocus_iff_equations (t : ℂ) (v : Fin 3 → ℂ) (hv : v ≠ 0)
    (w : Fin 4 → Fin 2 → ℂ) (hw : ∀ r, w r ≠ 0) :
    (Projectivization.mk ℂ v hv,(fun r => Projectivization.mk ℂ (w r) (hw r)),t) ∈ totalLocus ↔
      ∀ r, evaluate t v w (equation r) = 0 := by
  exact forall_congr' (incidence_iff_equation t v hv w hw)

/-- Pointwise zero-locus presentation for every point of the original ambient product. -/
theorem ambient_mem_totalLocus_iff (q : Ambient) :
    q ∈ totalLocus ↔ ∀ r, evaluate q.2.2 q.1.rep (fun r => (q.2.1 r).rep) (equation r) = 0 := by
  have h := totalLocus_iff_equations q.2.2 q.1.rep q.1.rep_nonzero
    (fun r => (q.2.1 r).rep) (fun r => (q.2.1 r).rep_nonzero)
  simpa only [Projectivization.mk_rep] using h

/-- Simultaneous rescaling transforms each polynomial by exactly its multidegree. -/
theorem evaluate_equation_rescale (t c : ℂ) (d : Fin 4 → ℂ)
    (v : Fin 3 → ℂ) (w : Fin 4 → Fin 2 → ℂ) (r : Fin 4) :
    evaluate t (c • v) (fun r => d r • w r) (equation r) =
      c * d r * evaluate t v w (equation r) := by
  simp only [evaluate_equation,map_smul,Pi.smul_apply,smul_eq_mul]
  ring

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.IncidenceEquations
