import FailureOfSemipositiveMetricExtension.GeneralCaoExtensionInterface
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Complex
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! Actual top-form and Lebesgue Jacobian identities in every complex dimension,
including dimension zero. No measure or determinant transformation is postulated. -/
namespace FailureOfSemipositiveMetricExtension.GeneralComplexJacobian
noncomputable section
open Set MeasureTheory
open scoped ENNReal

abbrev Coord (n : ℕ) := Fin n → ℂ

def determinant {n : ℕ} (A : Coord n →L[ℂ] Coord n) : ℂ := LinearMap.det A.toLinearMap

def jacobian {n : ℕ} (f : Coord n → Coord n) (q : Coord n) : ℂ := determinant (fderiv ℂ f q)

theorem coordinateVolume_comp {n : ℕ} (A : Coord n →L[ℂ] Coord n) :
    (GeneralCao.coordinateVolume n).compLinearMap A.toLinearMap =
      determinant A • GeneralCao.coordinateVolume n := by
  ext v
  exact Basis.det_comp (Pi.basisFun ℂ (Fin n)) A.toLinearMap v

theorem real_determinant_eq_normSq {n : ℕ} (A : Coord n →L[ℂ] Coord n) :
    (A.restrictScalars ℝ).toLinearMap.det = Complex.normSq (determinant A) := by
  change (A.toLinearMap.restrictScalars ℝ).det = _
  rw [LinearMap.det_restrictScalars,Algebra.norm_complex_apply]
  rfl

theorem abs_real_determinant {n : ℕ} (A : Coord n →L[ℂ] Coord n) :
    |(A.restrictScalars ℝ).toLinearMap.det| = Complex.normSq (determinant A) := by
  rw [real_determinant_eq_normSq,abs_of_nonneg (Complex.normSq_nonneg _)]

theorem lintegral_image_complex_jacobian {n : ℕ} {f : Coord n → Coord n} {S : Set (Coord n)}
    (hS : MeasurableSet S) (hf : ∀ q ∈ S, DifferentiableAt ℂ f q)
    (hinj : InjOn f S) (g : Coord n → ℝ≥0∞) :
    ∫⁻ q in f '' S, g q =
      ∫⁻ q in S, ENNReal.ofReal (Complex.normSq (jacobian f q)) * g (f q) := by
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul (μ := volume) hS
    (f' := fun q => (fderiv ℂ f q).restrictScalars ℝ)
    (fun q hq => ((hf q hq).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt) hinj g
  simpa only [abs_real_determinant,jacobian] using h

theorem jacobian_comp {n : ℕ} {f g : Coord n → Coord n} (q : Coord n)
    (hf : DifferentiableAt ℂ f q) (hg : DifferentiableAt ℂ g (f q)) :
    jacobian (g ∘ f) q = jacobian g (f q) * jacobian f q := by
  rw [jacobian,fderiv_comp q hg hf]
  exact LinearMap.det_comp _ _

@[simp] theorem jacobian_id {n : ℕ} (q : Coord n) : jacobian id q = 1 := by
  simp [jacobian,determinant]

end
end FailureOfSemipositiveMetricExtension.GeneralComplexJacobian
