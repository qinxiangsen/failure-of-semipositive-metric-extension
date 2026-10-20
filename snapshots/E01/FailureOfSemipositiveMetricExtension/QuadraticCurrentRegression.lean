import FailureOfSemipositiveMetricExtension.PshCurvatureCurrentInterface

/-! A non-real mixed Hessian regression: q(z)=|z0+i*z1|².
The actual real Frechet Hessian is computed, then its complex polarization has
upper-right entry -i and lower-left entry i. Its nonnegative Hermitian form is
squared modulus. The standard smooth-psh criterion is only a mathematical label
here, not a new axiom or an assumed test result. -/
namespace FailureOfSemipositiveMetricExtension.QuadraticCurrentRegression
noncomputable section
open FailureOfSemipositiveMetricExtension.WeakComplexHessian FailureOfSemipositiveMetricExtension.PshCurvatureCurrentInterface
open scoped ContDiff

abbrev Coord := ℂ × ℂ

def realPart : Coord →L[ℝ] ℝ :=
  Complex.reCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℂ) -
    Complex.imCLM.comp (ContinuousLinearMap.snd ℝ ℂ ℂ)

def imagPart : Coord →L[ℝ] ℝ :=
  Complex.imCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℂ) +
    Complex.reCLM.comp (ContinuousLinearMap.snd ℝ ℂ ℂ)

def quadratic (z : Coord) : ℝ := realPart z * realPart z + imagPart z * imagPart z

theorem quadratic_eq_normSq (z : Coord) :
    quadratic z = Complex.normSq (z.1 + Complex.I * z.2) := by
  simp [quadratic,realPart,imagPart,Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
  ring

theorem quadratic_nonnegative (z : Coord) : 0 ≤ quadratic z := by
  rw [quadratic_eq_normSq]
  exact Complex.normSq_nonneg _

def hessian : Coord →L[ℝ] (Coord →L[ℝ] ℝ) :=
  (2 : ℝ) • realPart.smulRight realPart + (2 : ℝ) • imagPart.smulRight imagPart

theorem quadratic_hasFDerivAt (z : Coord) : HasFDerivAt quadratic (hessian z) z := by
  have he : hessian z = realPart z • realPart + realPart z • realPart +
      (imagPart z • imagPart + imagPart z • imagPart) := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [hessian,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply,smul_eq_mul]
    ring
  rw [he]
  exact (realPart.hasFDerivAt.mul realPart.hasFDerivAt).add
    (imagPart.hasFDerivAt.mul imagPart.hasFDerivAt)

theorem quadratic_contDiff : ContDiff ℝ ∞ quadratic :=
  (realPart.contDiff.mul realPart.contDiff).add (imagPart.contDiff.mul imagPart.contDiff)

theorem quadratic_secondDirectional (v z : Coord) :
    secondDirectional v quadratic z = 2 * quadratic v := by
  have hder : fderiv ℝ quadratic = hessian := funext fun z => (quadratic_hasFDerivAt z).fderiv
  unfold secondDirectional
  rw [iteratedFDeriv_succ_apply_right,iteratedFDeriv_one_apply,hder,hessian.fderiv]
  simp [hessian,quadratic,Fin.init]
  ring

theorem quadratic_I_smul (v : Coord) : quadratic (Complex.I • v) = quadratic v := by
  simp [quadratic,realPart,imagPart,Complex.mul_re,Complex.mul_im]
  ring

theorem quadratic_complexLaplacian (v z : Coord) :
    complexLaplacian v quadratic z = 4 * Complex.normSq (v.1 + Complex.I * v.2) := by
  rw [complexLaplacian,quadratic_secondDirectional,quadratic_secondDirectional,
    quadratic_I_smul,quadratic_eq_normSq]
  ring

/-- The unnormalized complex Hessian evaluated on an arbitrary complex vector. -/
def hermitianValue (v : Coord) : ℝ := Complex.normSq (v.1 + Complex.I * v.2)

def polarizedMixed : ℂ := (1/4 : ℂ) *
  ((hermitianValue (unitVector 0 + unitVector 1) : ℂ) -
    (hermitianValue (unitVector 0 - unitVector 1) : ℂ) + Complex.I *
    ((hermitianValue (unitVector 0 + Complex.I • unitVector 1) : ℂ) -
      (hermitianValue (unitVector 0 - Complex.I • unitVector 1) : ℂ)))

theorem polarizedMixed_eq_neg_I : polarizedMixed = -Complex.I := by
  norm_num [polarizedMixed,hermitianValue,unitVector,Complex.normSq_apply]
  simp [Complex.ext_iff]

theorem conjugateMixed_eq_I : star polarizedMixed = Complex.I := by
  rw [polarizedMixed_eq_neg_I]
  simp

/-- Direct check of the coefficient convention v_j*conj(v_k)*H_jk, including
its imaginary mixed terms. -/
theorem hermitian_matrix_formula (v : Coord) :
    (v.1 * star v.1 + v.1 * star v.2 * (-Complex.I) +
      v.2 * star v.1 * Complex.I + v.2 * star v.2).re = hermitianValue v := by
  simp [hermitianValue,Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
  ring

theorem hermitian_matrix_nonnegative (v : Coord) :
    0 ≤ (v.1 * star v.1 + v.1 * star v.2 * (-Complex.I) +
      v.2 * star v.1 * Complex.I + v.2 * star v.2).re := by
  rw [hermitian_matrix_formula]
  exact Complex.normSq_nonneg _

/-- All coordinate derivatives of the constant Hessian coefficients vanish,
so both the partial and bar-partial closure directions pass this regression. -/
theorem constant_hessian_closed (a : ℂ) (v z : Coord) :
    fderiv ℝ (fun _ : Coord => a) z v = 0 := by simp

end
end FailureOfSemipositiveMetricExtension.QuadraticCurrentRegression
