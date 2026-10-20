import FailureOfSemipositiveMetricExtension.ComplexSurfaceJacobian
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Complex
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! Real volume change for genuine complex derivatives.  The real determinant
is proved to be the squared modulus of the complex determinant; no geometric
change-of-variables fact is admitted. -/
namespace FailureOfSemipositiveMetricExtension.ComplexSurfaceJacobian
noncomputable section
open Set MeasureTheory
open scoped ENNReal

theorem real_determinant_eq_normSq (A : Coord →L[ℂ] Coord) :
    (A.restrictScalars ℝ).toLinearMap.det = Complex.normSq (determinant A) := by
  change (A.toLinearMap.restrictScalars ℝ).det = _
  rw [LinearMap.det_restrictScalars,Algebra.norm_complex_apply]
  rfl

theorem abs_real_determinant (A : Coord →L[ℂ] Coord) :
    |(A.restrictScalars ℝ).toLinearMap.det| = Complex.normSq (determinant A) := by
  rw [real_determinant_eq_normSq,abs_of_nonneg (Complex.normSq_nonneg _)]

/-- The exact Lebesgue change-of-variables formula on a measurable set for an
injective complex-differentiable coordinate change. -/
theorem lintegral_image_complex_jacobian {f : Coord → Coord} {S : Set Coord}
    (hS : MeasurableSet S) (hf : ∀ q ∈ S, DifferentiableAt ℂ f q)
    (hinj : InjOn f S) (g : Coord → ℝ≥0∞) :
    ∫⁻ q in f '' S, g q =
      ∫⁻ q in S, ENNReal.ofReal (Complex.normSq (jacobian f q)) * g (f q) := by
  letI : (volume : Measure Coord).IsAddHaarMeasure := by
    change ((volume : Measure ℂ).prod (volume : Measure ℂ)).IsAddHaarMeasure
    infer_instance
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul (μ := volume) hS
    (f' := fun q => (fderiv ℂ f q).restrictScalars ℝ)
    (fun q hq => ((hf q hq).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt) hinj g
  simpa only [abs_real_determinant,jacobian] using h

end
end FailureOfSemipositiveMetricExtension.ComplexSurfaceJacobian
