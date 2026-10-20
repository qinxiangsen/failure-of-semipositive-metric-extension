import FailureOfSemipositiveMetricExtension.PshCurvatureCurrentInterface
import FailureOfSemipositiveMetricExtension.ComplexSurfaceJacobian

/-! Exact local coordinate/gauge covariance interface for distributional dd^c.
The coefficient transformation uses actual complex derivatives and the actual
inverse real-volume Jacobian. No external theorem is asserted in this file. -/
namespace FailureOfSemipositiveMetricExtension.CurrentCoordinateCovariance
noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
open WeakComplexHessian PshCurvatureCurrentInterface

abbrev Coord := ℂ × ℂ

def complexCoefficient (u : Coord → ℝ) (j k : Fin 2) (f : Coord → ℂ) : ℂ :=
  coefficient u j k (fun x => (f x).re) + Complex.I * coefficient u j k (fun x => (f x).im)

def IsComplexTest (U : Set Coord) (f : Coord → ℂ) : Prop :=
  IsTest U (fun x => (f x).re) ∧ IsTest U (fun x => (f x).im)

def component (a : Fin 2) (z : Coord) : ℂ := if a = 0 then z.1 else z.2

def derivativeEntry (F : Coord → Coord) (x : Coord) (a j : Fin 2) : ℂ :=
  component a (fderiv ℂ F x (unitVector j))

/-- A test density in y coordinates for the pullback coefficient in x
coordinates, where y=e(x). The inverse Jacobian is indispensable. -/
def transportedTest (e : PartialHomeomorph Coord Coord) (φ : Coord → ℝ)
    (j k a b : Fin 2) (y : Coord) : ℂ := by
  classical
  exact if y ∈ e.target then
    (φ (e.symm y) : ℂ) * derivativeEntry e (e.symm y) a j *
      star (derivativeEntry e (e.symm y) b k) *
      (Complex.normSq (ComplexSurfaceJacobian.jacobian e.symm y) : ℝ)
    else 0

/-- Precise generic distributional coordinate invariance plus the vanishing
of dd^c log|g|² for a nowhere-zero holomorphic gauge. All domains, tests,
extended-value representatives, Jacobians and indices are explicit. -/
def CovarianceStatement : Prop :=
  ∀ (e : PartialHomeomorph Coord Coord),
    ContDiffOn ℂ ω e e.source → ContDiffOn ℂ ω e.symm e.target →
    ∀ (u v : Coord → WithBot ℝ),
      LocallyIntegrableOn (realRepresentative u) e.source →
      LocallyIntegrableOn (realRepresentative v) e.target →
      (∀ᵐ x ∂volume.restrict e.source, u x ≠ ⊥) →
      (∀ᵐ y ∂volume.restrict e.target, v y ≠ ⊥) →
    ∀ (g : Coord → ℂ), ContDiffOn ℂ ω g e.source →
      (∀ x ∈ e.source, g x ≠ 0) →
      (∀ x ∈ e.source, u x = v (e x) + (Real.log (Complex.normSq (g x)) : ℝ)) →
      ∀ (φ : Coord → ℝ), IsTest e.source φ →
        (∀ j k a b, IsComplexTest e.target (transportedTest e φ j k a b)) ∧
        ∀ j k, coefficient (realRepresentative u) j k φ =
          ∑ a : Fin 2, ∑ b : Fin 2,
            complexCoefficient (realRepresentative v) a b (transportedTest e φ j k a b)

@[simp] theorem coefficient_zero (u : Coord → ℝ) (j k : Fin 2) :
    coefficient u j k (fun _ => 0) = 0 := by
  have hz : (fun _ : Coord => (0 : ℝ)) = (0 : ℝ) • (fun _ : Coord => (0 : ℝ)) := by ext; simp
  conv_lhs => rw [hz]
  rw [coefficient_smul u contDiff_const]
  simp

@[simp] theorem complexCoefficient_ofReal (u : Coord → ℝ) (j k : Fin 2) (φ : Coord → ℝ) :
    complexCoefficient u j k (fun x => (φ x : ℂ)) = coefficient u j k φ := by
  simp [complexCoefficient]

@[simp] theorem complexCoefficient_zero (u : Coord → ℝ) (j k : Fin 2) :
    complexCoefficient u j k (fun _ => 0) = 0 := by simp [complexCoefficient]

@[simp] theorem derivativeEntry_id (x : Coord) (a j : Fin 2) :
    derivativeEntry id x a j = if a = j then 1 else 0 := by
  fin_cases a <;> fin_cases j <;> simp [derivativeEntry,component,unitVector]

@[simp] theorem transportedTest_refl (φ : Coord → ℝ) (j k a b : Fin 2) :
    transportedTest (PartialHomeomorph.refl Coord) φ j k a b =
      if a = j ∧ b = k then (fun x => (φ x : ℂ)) else (fun _ => 0) := by
  ext y
  simp only [transportedTest,PartialHomeomorph.refl_target,mem_univ,ite_true,
    PartialHomeomorph.refl_symm]
  change (φ y : ℂ) * derivativeEntry id y a j * star (derivativeEntry id y b k) *
    (Complex.normSq (ComplexSurfaceJacobian.jacobian id y) : ℝ) = _
  rw [derivativeEntry_id,derivativeEntry_id,ComplexSurfaceJacobian.jacobian_id]
  split_ifs <;> simp_all

/-- The identity coordinate change reduces the distribution formula to itself,
including off-diagonal coefficients. -/
theorem covariance_refl_formula (u : Coord → ℝ) (φ : Coord → ℝ) (j k : Fin 2) :
    coefficient u j k φ = ∑ a : Fin 2, ∑ b : Fin 2,
      complexCoefficient u a b (transportedTest (PartialHomeomorph.refl Coord) φ j k a b) := by
  fin_cases j <;> fin_cases k <;>
    simp [Fin.sum_univ_two,transportedTest_refl,complexCoefficient_ofReal]

/-- Imaginary shear regression: the transformed upper-right Hessian entry of
|z0|² under (z0+i*z1,z1) is -i, with this precise conjugation direction. -/
def imaginaryShear : Coord →L[ℂ] Coord :=
  ((ContinuousLinearMap.fst ℂ ℂ ℂ) + Complex.I • ContinuousLinearMap.snd ℂ ℂ ℂ).prod
    (ContinuousLinearMap.snd ℂ ℂ ℂ)

theorem imaginaryShear_mixed_sign (x : Coord) :
    derivativeEntry imaginaryShear x 0 0 * star (derivativeEntry imaginaryShear x 0 1) = -Complex.I := by
  simp [derivativeEntry,imaginaryShear,component,unitVector,Complex.star_def]

end
end FailureOfSemipositiveMetricExtension.CurrentCoordinateCovariance
