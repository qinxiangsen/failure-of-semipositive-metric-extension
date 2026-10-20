import FailureOfSemipositiveMetricExtension.Cubics
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Ideal.Operations

/-!
# The affine first jets of the explicit cubic and conic systems

This file connects the coefficient predicates in `Cubics` to analytic first
Taylor data in the affine chart `z = 1`. All derivatives below are actual
complex derivatives, not formal placeholders for coefficient conditions.
-/

noncomputable section

namespace FailureOfSemipositiveMetricExtension.Jets
open FailureOfSemipositiveMetricExtension.Cubics

/-- The value at the affine origin is the constant coefficient. -/
theorem cubic_value_origin (c : Cubic) : c.eval 0 0 1 = c.zzz := by
  simp [Cubic.eval]

theorem cubic_hasDerivAt_x_origin (c : Cubic) :
    HasDerivAt (fun x : ℂ => c.eval x 0 1) c.xzz 0 := by
  simpa [Cubic.eval] using
    ((((hasDerivAt_pow 3 (0 : ℂ)).const_mul c.xxx).add
      ((hasDerivAt_pow 2 (0 : ℂ)).const_mul c.xxz)).add
      ((hasDerivAt_id (0 : ℂ)).const_mul c.xzz)).add_const c.zzz

theorem cubic_hasDerivAt_y_origin (c : Cubic) :
    HasDerivAt (fun y : ℂ => c.eval 0 y 1) c.yzz 0 := by
  simpa [Cubic.eval] using
    ((((hasDerivAt_pow 3 (0 : ℂ)).const_mul c.yyy).add
      ((hasDerivAt_pow 2 (0 : ℂ)).const_mul c.yyz)).add
      ((hasDerivAt_id (0 : ℂ)).const_mul c.yzz)).add_const c.zzz

theorem cubic_deriv_x_origin (c : Cubic) :
    deriv (fun x : ℂ => c.eval x 0 1) 0 = c.xzz :=
  (cubic_hasDerivAt_x_origin c).deriv

theorem cubic_deriv_y_origin (c : Cubic) :
    deriv (fun y : ℂ => c.eval 0 y 1) 0 = c.yzz :=
  (cubic_hasDerivAt_y_origin c).deriv

/-- Double vanishing means precisely zero value and zero first partial derivatives. -/
theorem cubic_doubleAtP4_iff_first_jet (c : Cubic) :
    c.doubleAtP4 ↔ c.eval 0 0 1 = 0 ∧
      deriv (fun x : ℂ => c.eval x 0 1) 0 = 0 ∧
      deriv (fun y : ℂ => c.eval 0 y 1) 0 = 0 := by
  rw [cubic_value_origin, cubic_deriv_x_origin, cubic_deriv_y_origin]
  rfl

/-- An exact second-order Taylor decomposition, with a polynomial remainder. -/
theorem cubic_taylor_decomposition (c : Cubic) (x y : ℂ) :
    c.eval x y 1 = c.zzz + c.xzz*x + c.yzz*y +
      x^2*(c.xxx*x + c.xxy*y + c.xxz) +
      x*y*(c.xyy*y + c.xyz) + y^2*(c.yyy*y + c.yyz) := by
  unfold Cubic.eval
  ring

theorem conic_value_origin (c : Conic) : c.eval 0 0 1 = c.zz := by
  simp [Conic.eval]

theorem conic_hasDerivAt_x_origin (c : Conic) :
    HasDerivAt (fun x : ℂ => c.eval x 0 1) c.xz 0 := by
  simpa [Conic.eval] using
    (((hasDerivAt_pow 2 (0 : ℂ)).const_mul c.xx).add
      ((hasDerivAt_id (0 : ℂ)).const_mul c.xz)).add_const c.zz

theorem conic_hasDerivAt_y_origin (c : Conic) :
    HasDerivAt (fun y : ℂ => c.eval 0 y 1) c.yz 0 := by
  simpa [Conic.eval] using
    (((hasDerivAt_pow 2 (0 : ℂ)).const_mul c.yy).add
      ((hasDerivAt_id (0 : ℂ)).const_mul c.yz)).add_const c.zz

theorem conic_deriv_x_origin (c : Conic) :
    deriv (fun x : ℂ => c.eval x 0 1) 0 = c.xz :=
  (conic_hasDerivAt_x_origin c).deriv

theorem conic_deriv_y_origin (c : Conic) :
    deriv (fun y : ℂ => c.eval 0 y 1) 0 = c.yz :=
  (conic_hasDerivAt_y_origin c).deriv

theorem conic_doubleAtP4_iff_first_jet (c : Conic) :
    c.doubleAtP4 ↔ c.eval 0 0 1 = 0 ∧
      deriv (fun x : ℂ => c.eval x 0 1) 0 = 0 ∧
      deriv (fun y : ℂ => c.eval 0 y 1) 0 = 0 := by
  rw [conic_value_origin, conic_deriv_x_origin, conic_deriv_y_origin]
  rfl

theorem conic_taylor_decomposition (c : Conic) (x y : ℂ) :
    c.eval x y 1 = c.zz + c.xz*x + c.yz*y +
      c.xx*x^2 + c.xy*x*y + c.yy*y^2 := by
  unfold Conic.eval
  ring

/-! ## The square of the affine origin ideal -/

open MvPolynomial

abbrev AffinePolynomial := MvPolynomial (Fin 2) ℂ

/-- The ordinary polynomial ideal `(x,y)` of the affine origin. -/
def originIdeal : Ideal AffinePolynomial := Ideal.span {X 0, X 1}

/-- The dehomogenized cubic as an actual bivariate polynomial. -/
def cubicAffinePolynomial (c : Cubic) : AffinePolynomial :=
  C c.xxx*X 0^3 + C c.xxy*X 0^2*X 1 + C c.xyy*X 0*X 1^2 + C c.yyy*X 1^3 +
  C c.xxz*X 0^2 + C c.xyz*X 0*X 1 + C c.yyz*X 1^2 +
  C c.xzz*X 0 + C c.yzz*X 1 + C c.zzz

/-- The dehomogenized conic as an actual bivariate polynomial. -/
def conicAffinePolynomial (c : Conic) : AffinePolynomial :=
  C c.xx*X 0^2 + C c.xy*X 0*X 1 + C c.yy*X 1^2 +
  C c.xz*X 0 + C c.yz*X 1 + C c.zz

theorem cubicAffinePolynomial_eval (c : Cubic) (x y : ℂ) :
    eval ![x,y] (cubicAffinePolynomial c) = c.eval x y 1 := by
  simp [cubicAffinePolynomial, Cubic.eval]

theorem conicAffinePolynomial_eval (c : Conic) (x y : ℂ) :
    eval ![x,y] (conicAffinePolynomial c) = c.eval x y 1 := by
  simp [conicAffinePolynomial, Conic.eval]

theorem originIdeal_eval_zero {p : AffinePolynomial} (hp : p ∈ originIdeal) :
    eval (fun _ => (0 : ℂ)) p = 0 := by
  have hle : originIdeal ≤ RingHom.ker (eval (fun _ : Fin 2 => (0 : ℂ))) := by
    apply Ideal.span_le.mpr
    intro q hq
    rcases Set.mem_insert_iff.mp hq with rfl | hq
    · simp
    · have : q = X 1 := Set.mem_singleton_iff.mp hq
      subst q
      simp
  exact hle hp

/-- Every polynomial in `(x,y)^2` has zero algebraic first jet. -/
theorem originIdeal_sq_first_jet {p : AffinePolynomial} (hp : p ∈ originIdeal^2) :
    eval (fun _ => (0 : ℂ)) p = 0 ∧
      ∀ i : Fin 2, eval (fun _ => (0 : ℂ)) (pderiv i p) = 0 := by
  rw [pow_two] at hp
  refine Submodule.mul_induction_on hp ?_ ?_
  · intro p hp q hq
    have hp0 := originIdeal_eval_zero hp
    have hq0 := originIdeal_eval_zero hq
    constructor
    · simp only [map_mul, hp0, hq0, zero_mul]
    · intro i
      simp only [pderiv_mul, map_mul, map_add, hp0, hq0, zero_mul, mul_zero, zero_add]
  · intro p q hp hq
    constructor
    · simp only [map_add, hp.1, hq.1, zero_add]
    · intro i
      simp only [map_add, hp.2 i, hq.2 i, zero_add]

/-- Any explicit combination of the three quadratic generators is in `(x,y)^2`. -/
theorem quadratic_combination_mem_originIdeal_sq (a b c : AffinePolynomial) :
    X 0^2*a + (X 0*X 1)*b + X 1^2*c ∈ originIdeal^2 := by
  have hx : (X 0 : AffinePolynomial) ∈ originIdeal := Ideal.subset_span (by simp)
  have hy : (X 1 : AffinePolynomial) ∈ originIdeal := Ideal.subset_span (by simp)
  have hxx : (X 0 : AffinePolynomial)^2 ∈ originIdeal^2 := Ideal.pow_mem_pow hx 2
  have hxy : (X 0 : AffinePolynomial)*X 1 ∈ originIdeal^2 := by
    simpa [pow_two] using Ideal.mul_mem_mul hx hy
  have hyy : (X 1 : AffinePolynomial)^2 ∈ originIdeal^2 := Ideal.pow_mem_pow hy 2
  exact (originIdeal^2).add_mem
    ((originIdeal^2).add_mem ((originIdeal^2).mul_mem_right a hxx)
      ((originIdeal^2).mul_mem_right b hxy))
    ((originIdeal^2).mul_mem_right c hyy)

theorem cubicAffinePolynomial_first_jet (c : Cubic) :
    eval (fun _ => (0 : ℂ)) (cubicAffinePolynomial c) = c.zzz ∧
      eval (fun _ => (0 : ℂ)) (pderiv 0 (cubicAffinePolynomial c)) = c.xzz ∧
      eval (fun _ => (0 : ℂ)) (pderiv 1 (cubicAffinePolynomial c)) = c.yzz := by
  simp [cubicAffinePolynomial, pderiv_mul, pderiv_pow, pderiv_C_mul, pderiv_C]

theorem conicAffinePolynomial_first_jet (c : Conic) :
    eval (fun _ => (0 : ℂ)) (conicAffinePolynomial c) = c.zz ∧
      eval (fun _ => (0 : ℂ)) (pderiv 0 (conicAffinePolynomial c)) = c.xz ∧
      eval (fun _ => (0 : ℂ)) (pderiv 1 (conicAffinePolynomial c)) = c.yz := by
  simp [conicAffinePolynomial, pderiv_mul, pderiv_pow, pderiv_C_mul, pderiv_C]

/-- Coefficient double vanishing is exactly membership in the square of `(x,y)`. -/
theorem cubic_doubleAtP4_iff_mem_originIdeal_sq (c : Cubic) :
    c.doubleAtP4 ↔ cubicAffinePolynomial c ∈ originIdeal^2 := by
  constructor
  · rintro ⟨hzzz, hxzz, hyzz⟩
    have heq : cubicAffinePolynomial c =
        X 0^2*(C c.xxx*X 0 + C c.xxy*X 1 + C c.xxz) +
        (X 0*X 1)*(C c.xyy*X 1 + C c.xyz) +
        X 1^2*(C c.yyy*X 1 + C c.yyz) := by
      simp only [cubicAffinePolynomial, hzzz, hxzz, hyzz, map_zero]
      ring
    rw [heq]
    exact quadratic_combination_mem_originIdeal_sq _ _ _
  · intro hp
    have hj := originIdeal_sq_first_jet hp
    have hc := cubicAffinePolynomial_first_jet c
    exact ⟨hc.1.symm.trans hj.1,
      hc.2.1.symm.trans (hj.2 0), hc.2.2.symm.trans (hj.2 1)⟩

theorem conic_doubleAtP4_iff_mem_originIdeal_sq (c : Conic) :
    c.doubleAtP4 ↔ conicAffinePolynomial c ∈ originIdeal^2 := by
  constructor
  · rintro ⟨hzz, hxz, hyz⟩
    have heq : conicAffinePolynomial c =
        X 0^2*C c.xx + (X 0*X 1)*C c.xy + X 1^2*C c.yy := by
      simp only [conicAffinePolynomial, hzz, hxz, hyz, map_zero]
      ring
    rw [heq]
    exact quadratic_combination_mem_originIdeal_sq _ _ _
  · intro hp
    have hj := originIdeal_sq_first_jet hp
    have hc := conicAffinePolynomial_first_jet c
    exact ⟨hc.1.symm.trans hj.1,
      hc.2.1.symm.trans (hj.2 0), hc.2.2.symm.trans (hj.2 1)⟩

/-! ## Geometric inputs stated using actual complex first derivatives -/

/-- The affine cubic is a complex differentiable function of both coordinates. -/
theorem cubic_affine_differentiable (c : Cubic) :
    Differentiable ℂ (fun p : ℂ × ℂ => c.eval p.1 p.2 1) := by
  unfold Cubic.eval
  fun_prop

theorem conic_affine_differentiable (c : Conic) :
    Differentiable ℂ (fun p : ℂ × ℂ => c.eval p.1 p.2 1) := by
  unfold Conic.eval
  fun_prop

/-- The paper's displayed cubic spanning statement with analytic jet hypotheses. -/
theorem cubic_span_of_first_jet (c : Cubic)
    (h₁ : c.eval 1 0 0 = 0) (h₂ : c.eval 0 1 0 = 0)
    (h₃ : c.eval 1 1 0 = 0) (hvalue : c.eval 0 0 1 = 0)
    (hx : deriv (fun x : ℂ => c.eval x 0 1) 0 = 0)
    (hy : deriv (fun y : ℂ => c.eval 0 y 1) 0 = 0) :
    ∀ x y z : ℂ, c.eval x y z =
      c.xxz*(x^2*z) + c.xyz*(x*y*z) + c.yyz*(y^2*z) + c.xxy*(x*y*(x-y)) :=
  cubic_span c h₁ h₂ h₃ ((cubic_doubleAtP4_iff_first_jet c).mpr ⟨hvalue,hx,hy⟩)

/-- The `m=3` conic impossibility with actual value-and-derivative hypotheses. -/
theorem conic_eval_zero_of_first_jet (c : Conic)
    (h₁ : c.eval 1 0 0 = 0) (h₂ : c.eval 0 1 0 = 0)
    (h₃ : c.eval 1 1 0 = 0) (hvalue : c.eval 0 0 1 = 0)
    (hx : deriv (fun x : ℂ => c.eval x 0 1) 0 = 0)
    (hy : deriv (fun y : ℂ => c.eval 0 y 1) 0 = 0) :
    ∀ x y z : ℂ, c.eval x y z = 0 :=
  conic_eval_zero c h₁ h₂ h₃ ((conic_doubleAtP4_iff_first_jet c).mpr ⟨hvalue,hx,hy⟩)

end FailureOfSemipositiveMetricExtension.Jets
