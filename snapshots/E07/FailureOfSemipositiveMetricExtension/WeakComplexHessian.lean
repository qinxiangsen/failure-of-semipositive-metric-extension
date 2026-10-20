import FailureOfSemipositiveMetricExtension.LogarithmicOrder
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Actual compactly supported smooth tests and weak second derivatives on C².
No existence or positivity theorem for psh weights is assumed in this module. -/
namespace FailureOfSemipositiveMetricExtension.WeakComplexHessian
noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff

abbrev Coord := ℂ × ℂ

def IsTest (U : Set Coord) (f : Coord → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ U

def secondDirectional (v : Coord) (f : Coord → ℝ) (x : Coord) : ℝ :=
  iteratedFDeriv ℝ 2 f x (fun _ : Fin 2 => v)

def complexLaplacian (v : Coord) (f : Coord → ℝ) (x : Coord) : ℝ :=
  secondDirectional v f x + secondDirectional (Complex.I • v) f x

def laplacian (f : Coord → ℝ) (x : Coord) : ℝ :=
  complexLaplacian (1,0) f x + complexLaplacian (0,1) f x

/-- The arbitrary value at minus infinity is used only with an explicit local-L¹
hypothesis, never as a convention that could make a divergent integral finite. -/
def realRepresentative (u : Coord → WithBot ℝ) (x : Coord) : ℝ :=
  (u x).unbotD 0

def weakDirectional (u : Coord → ℝ) (v : Coord) (f : Coord → ℝ) : ℝ :=
  ∫ x, u x * complexLaplacian v f x

def weakTrace (u : Coord → ℝ) (f : Coord → ℝ) : ℝ :=
  (4 * Real.pi)⁻¹ * ∫ x, u x * laplacian f x

theorem secondDirectional_continuous {f : Coord → ℝ}
    (hf : ContDiff ℝ ∞ f) (v : Coord) : Continuous (secondDirectional v f) := by
  have hc := hf.continuous_iteratedFDeriv (m := 2) (by exact WithTop.coe_le_coe.mpr le_top)
  exact hc.eval_const (fun _ : Fin 2 => v)

theorem complexLaplacian_continuous {f : Coord → ℝ}
    (hf : ContDiff ℝ ∞ f) (v : Coord) : Continuous (complexLaplacian v f) :=
  (secondDirectional_continuous hf v).add (secondDirectional_continuous hf _)

theorem laplacian_continuous {f : Coord → ℝ}
    (hf : ContDiff ℝ ∞ f) : Continuous (laplacian f) :=
  (complexLaplacian_continuous hf _).add (complexLaplacian_continuous hf _)

theorem secondDirectional_eq_zero_of_not_mem_tsupport (f : Coord → ℝ)
    (v x : Coord) (hx : x ∉ tsupport f) : secondDirectional v f x = 0 := by
  have hh : iteratedFDeriv ℝ 2 f x = 0 := by
    by_contra h
    exact hx (support_iteratedFDeriv_subset 2 h)
  simp [secondDirectional,hh]

theorem complexLaplacian_eq_zero_of_not_mem_tsupport (f : Coord → ℝ)
    (v x : Coord) (hx : x ∉ tsupport f) : complexLaplacian v f x = 0 := by
  simp [complexLaplacian,secondDirectional_eq_zero_of_not_mem_tsupport f _ x hx]

theorem laplacian_eq_zero_of_not_mem_tsupport (f : Coord → ℝ)
    (x : Coord) (hx : x ∉ tsupport f) : laplacian f x = 0 := by
  simp [laplacian,complexLaplacian_eq_zero_of_not_mem_tsupport f _ x hx]

theorem locallyIntegrable_mul_test {U : Set Coord} {u g f : Coord → ℝ}
    (hu : LocallyIntegrableOn u U) (hf : IsTest U f) (hg : Continuous g)
    (hs : ∀ x, x ∉ tsupport f → g x = 0) : Integrable (fun x => u x * g x) := by
  have hi := (hu.integrableOn_compact_subset hf.2.2 hf.2.1).mul_continuousOn
    hg.continuousOn hf.2.1
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hi
  intro x hx
  by_contra hn
  exact hx (by simp [hs x hn])

theorem complexLaplacian_integrable {U : Set Coord} {u f : Coord → ℝ}
    (hu : LocallyIntegrableOn u U) (hf : IsTest U f) (v : Coord) :
    Integrable (fun x => u x * complexLaplacian v f x) :=
  locallyIntegrable_mul_test hu hf (complexLaplacian_continuous hf.1 v)
    (complexLaplacian_eq_zero_of_not_mem_tsupport f v)

theorem laplacian_integrable {U : Set Coord} {u f : Coord → ℝ}
    (hu : LocallyIntegrableOn u U) (hf : IsTest U f) :
    Integrable (fun x => u x * laplacian f x) :=
  locallyIntegrable_mul_test hu hf (laplacian_continuous hf.1)
    (laplacian_eq_zero_of_not_mem_tsupport f)

theorem secondDirectional_add {f g : Coord → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (v x : Coord) :
    secondDirectional v (f+g) x = secondDirectional v f x + secondDirectional v g x := by
  simp only [secondDirectional,iteratedFDeriv_add_apply
    (hf.of_le (by exact WithTop.coe_le_coe.mpr le_top)).contDiffAt
    (hg.of_le (by exact WithTop.coe_le_coe.mpr le_top)).contDiffAt]
  rfl

theorem complexLaplacian_add {f g : Coord → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (v x : Coord) :
    complexLaplacian v (f+g) x = complexLaplacian v f x + complexLaplacian v g x := by
  simp only [complexLaplacian,secondDirectional_add hf hg]
  ring

theorem laplacian_add {f g : Coord → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : Coord) :
    laplacian (f+g) x = laplacian f x + laplacian g x := by
  simp only [laplacian,complexLaplacian_add hf hg]
  ring

theorem secondDirectional_smul {f : Coord → ℝ}
    (hf : ContDiff ℝ ∞ f) (a : ℝ) (v x : Coord) :
    secondDirectional v (a • f) x = a * secondDirectional v f x := by
  simp only [secondDirectional,iteratedFDeriv_const_smul_apply
    (hf.of_le (by exact WithTop.coe_le_coe.mpr le_top)).contDiffAt]
  rfl

theorem complexLaplacian_smul {f : Coord → ℝ}
    (hf : ContDiff ℝ ∞ f) (a : ℝ) (v x : Coord) :
    complexLaplacian v (a • f) x = a * complexLaplacian v f x := by
  simp only [complexLaplacian,secondDirectional_smul hf]
  ring

theorem laplacian_smul {f : Coord → ℝ}
    (hf : ContDiff ℝ ∞ f) (a : ℝ) (x : Coord) :
    laplacian (a • f) x = a * laplacian f x := by
  simp only [laplacian,complexLaplacian_smul hf]
  ring

theorem weakTrace_add {U : Set Coord} {u f g : Coord → ℝ}
    (hu : LocallyIntegrableOn u U) (hf : IsTest U f) (hg : IsTest U g) :
    weakTrace u (f+g) = weakTrace u f + weakTrace u g := by
  simp only [weakTrace,laplacian_add hf.1 hg.1,mul_add]
  rw [integral_add (laplacian_integrable hu hf) (laplacian_integrable hu hg)]
  ring

theorem weakTrace_smul {f : Coord → ℝ} (u : Coord → ℝ)
    (hf : ContDiff ℝ ∞ f) (a : ℝ) : weakTrace u (a • f) = a * weakTrace u f := by
  simp only [weakTrace,laplacian_smul hf]
  simp_rw [← mul_assoc, mul_comm (u _) a, mul_assoc a]
  rw [integral_const_mul]
  ring

end
end FailureOfSemipositiveMetricExtension.WeakComplexHessian
