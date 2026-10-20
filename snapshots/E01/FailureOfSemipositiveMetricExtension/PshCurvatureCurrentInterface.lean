import FailureOfSemipositiveMetricExtension.WeakCurvatureDistribution
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! An explicit coordinate current, not an opaque synonym for logarithmic growth.
Its coefficients are polarized distributional second derivatives of the weight.
The trace is a genuine positive Borel measure representing its weak Laplacian.
The convention is dd^c = i/(2*pi) partial bar-partial, as in the paper. -/
namespace FailureOfSemipositiveMetricExtension.PshCurvatureCurrentInterface
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff ENNReal
open WeakComplexHessian

abbrev Coord := ℂ × ℂ

def unitVector (j : Fin 2) : Coord := if j = 0 then (1,0) else (0,1)

def firstDirectional (v : Coord) (f : Coord → ℝ) (x : Coord) : ℝ :=
  fderiv ℝ f x v

/-- The diagonal complex Hessian coefficient distribution. -/
def diagonalCoefficient (u : Coord → ℝ) (v : Coord) (f : Coord → ℝ) : ℂ :=
  ((8 * Real.pi)⁻¹ * weakDirectional u v f : ℝ)

/-- Polarization recovers the mixed coefficient of i dz_0 wedge dbar z_1. -/
def offDiagonalCoefficient (u : Coord → ℝ) (f : Coord → ℝ) : ℂ :=
  (1/4 : ℂ) * (diagonalCoefficient u (unitVector 0 + unitVector 1) f -
    diagonalCoefficient u (unitVector 0 - unitVector 1) f + Complex.I *
    (diagonalCoefficient u (unitVector 0 + Complex.I • unitVector 1) f -
      diagonalCoefficient u (unitVector 0 - Complex.I • unitVector 1) f))

def coefficient (u : Coord → ℝ) (j k : Fin 2) (f : Coord → ℝ) : ℂ :=
  if j = 0 then
    if k = 0 then diagonalCoefficient u (unitVector 0) f else offDiagonalCoefficient u f
  else
    if k = 0 then star (offDiagonalCoefficient u f) else diagonalCoefficient u (unitVector 1) f

/-- Order-at-most-two continuity in the usual compact-test-function topology. -/
def CoefficientOrderTwo (u : Coord → ℝ) (U : Set Coord) : Prop :=
  ∀ K, IsCompact K → K ⊆ U → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (f : Coord → ℝ), IsTest U f → tsupport f ⊆ K → ∀ M : ℝ, 0 ≤ M →
      (∀ x ∈ K, ‖iteratedFDeriv ℝ 2 f x‖ ≤ M) →
      ∀ j k, ‖coefficient u j k f‖ ≤ C * M

/-- Complex Hessian matrix positivity, in the positive-distribution sense. -/
def PositiveCoefficients (u : Coord → ℝ) (U : Set Coord) : Prop :=
  ∀ (v : Fin 2 → ℂ) (f : Coord → ℝ), IsTest U f → (∀ x, 0 ≤ f x) →
    0 ≤ (∑ j : Fin 2, ∑ k : Fin 2, v j * star (v k) * coefficient u j k f).re

/-- Distributional partial-closedness, written on real tests. The common factors
-1/2 from integration by parts and complex differentiation cancel on both sides. -/
def HolomorphicallyClosed (u : Coord → ℝ) (U : Set Coord) : Prop :=
  ∀ (f : Coord → ℝ), IsTest U f → ∀ l j k : Fin 2,
    coefficient u j k (firstDirectional (unitVector l) f) -
      Complex.I * coefficient u j k (firstDirectional (Complex.I • unitVector l) f) =
    coefficient u l k (firstDirectional (unitVector j) f) -
      Complex.I * coefficient u l k (firstDirectional (Complex.I • unitVector j) f)

def AntiholomorphicallyClosed (u : Coord → ℝ) (U : Set Coord) : Prop :=
  ∀ (f : Coord → ℝ), IsTest U f → ∀ l j k : Fin 2,
    coefficient u j k (firstDirectional (unitVector l) f) +
      Complex.I * coefficient u j k (firstDirectional (Complex.I • unitVector l) f) =
    coefficient u j l (firstDirectional (unitVector k) f) +
      Complex.I * coefficient u j l (firstDirectional (Complex.I • unitVector k) f)

/-- A true locally finite positive trace measure for the explicitly computed
closed positive (1,1) distributional curvature. No paper-specific object occurs. -/
structure CurvatureCurrent (u : Coord → WithBot ℝ) (U : Set Coord) where
  locallyIntegrable : LocallyIntegrableOn (realRepresentative u) U
  finite_ae : ∀ᵐ x ∂volume.restrict U, u x ≠ ⊥
  orderTwo : CoefficientOrderTwo (realRepresentative u) U
  positive : PositiveCoefficients (realRepresentative u) U
  closed_holomorphic : HolomorphicallyClosed (realRepresentative u) U
  closed_antiholomorphic : AntiholomorphicallyClosed (realRepresentative u) U
  traceMeasure : Measure Coord
  trace_outside : traceMeasure Uᶜ = 0
  trace_finite_compact : ∀ K, IsCompact K → K ⊆ U → traceMeasure K < ⊤
  trace_pairing : ∀ f, IsTest U f →
    (∫ x, f x ∂traceMeasure) = weakTrace (realRepresentative u) f

/-- Euclidean balls, rather than the max-norm balls of the default product norm. -/
def euclideanBall (p : Coord) (r : ℝ) : Set Coord :=
  {z | Complex.normSq (z.1-p.1) + Complex.normSq (z.2-p.2) < r^2}

def lelongRatio {u : Coord → WithBot ℝ} {U : Set Coord}
    (T : CurvatureCurrent u U) (p : Coord) (r : ℝ) : ℝ :=
  (T.traceMeasure (euclideanBall p r)).toReal / (Real.pi * r^2)

/-- The Lelong number is specified by its actual trace-mass limit. -/
def HasLelongNumber {u : Coord → WithBot ℝ} {U : Set Coord}
    (T : CurvatureCurrent u U) (p : Coord) (a : ℝ) : Prop :=
  Tendsto (lelongRatio T p) (𝓝[>] 0) (𝓝 a)

theorem HasLelongNumber.unique {u : Coord → WithBot ℝ} {U : Set Coord}
    {T : CurvatureCurrent u U} {p : Coord} {a b : ℝ}
    (ha : HasLelongNumber T p a) (hb : HasLelongNumber T p b) : a = b :=
  tendsto_nhds_unique ha hb

theorem diagonalCoefficient_add {U : Set Coord} {u f g : Coord → ℝ}
    (hu : LocallyIntegrableOn u U) (hf : IsTest U f) (hg : IsTest U g) (v : Coord) :
    diagonalCoefficient u v (f+g) = diagonalCoefficient u v f + diagonalCoefficient u v g := by
  simp only [diagonalCoefficient,weakDirectional_add hu hf hg,mul_add,Complex.ofReal_add]

theorem diagonalCoefficient_smul {f : Coord → ℝ} (u : Coord → ℝ)
    (hf : ContDiff ℝ ∞ f) (a : ℝ) (v : Coord) :
    diagonalCoefficient u v (a • f) = (a : ℂ) * diagonalCoefficient u v f := by
  simp only [diagonalCoefficient,weakDirectional_smul u hf,Complex.ofReal_mul]
  ring

theorem coefficient_add {U : Set Coord} {u f g : Coord → ℝ}
    (hu : LocallyIntegrableOn u U) (hf : IsTest U f) (hg : IsTest U g) (j k : Fin 2) :
    coefficient u j k (f+g) = coefficient u j k f + coefficient u j k g := by
  unfold coefficient offDiagonalCoefficient
  simp only [diagonalCoefficient_add hu hf hg]
  split_ifs <;> try simp only [Complex.star_def,map_add,map_mul,map_sub]
  all_goals ring

theorem coefficient_smul {f : Coord → ℝ} (u : Coord → ℝ)
    (hf : ContDiff ℝ ∞ f) (a : ℝ) (j k : Fin 2) :
    coefficient u j k (a • f) = (a : ℂ) * coefficient u j k f := by
  unfold coefficient offDiagonalCoefficient
  simp only [diagonalCoefficient_smul u hf]
  split_ifs <;> try simp only [map_add,map_mul,map_sub,Complex.star_def,Complex.conj_ofReal]
  all_goals ring

def coefficientLinearMap {U : Set Coord} (u : Coord → ℝ)
    (hu : LocallyIntegrableOn u U) (j k : Fin 2) : tests U →ₗ[ℝ] ℂ where
  toFun f := coefficient u j k f
  map_add' f g := coefficient_add hu f.property g.property j k
  map_smul' a f := by simpa using coefficient_smul u f.property.1 a j k

theorem weakTrace_eq_coefficient_trace {U : Set Coord} {u f : Coord → ℝ}
    (hu : LocallyIntegrableOn u U) (hf : IsTest U f) :
    (weakTrace u f : ℂ) = 2 * (coefficient u 0 0 f + coefficient u 1 1 f) := by
  rw [weakTrace_eq_sum hu hf]
  norm_num only [coefficient,unitVector,Fin.zero_eta,ite_true,ite_false,
    diagonalCoefficient,Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_inv,
    Complex.ofReal_ofNat,show (1 : Fin 2) ≠ 0 by decide]
  field_simp
  ring

theorem CurvatureCurrent.test_integrable {u : Coord → WithBot ℝ} {U : Set Coord}
    (T : CurvatureCurrent u U) {f : Coord → ℝ} (hf : IsTest U f) :
    Integrable f T.traceMeasure := by
  letI : IsFiniteMeasure (T.traceMeasure.restrict (tsupport f)) :=
    isFiniteMeasure_restrict.mpr (T.trace_finite_compact _ hf.2.1 hf.2.2).ne
  apply (integrableOn_iff_integrable_of_support_subset (subset_tsupport f)).mp
  exact hf.1.continuous.integrable_of_hasCompactSupport hf.2.1

theorem euclideanBall_subset_ball (p : Coord) (r : ℝ) (hr : 0 < r) :
    euclideanBall p r ⊆ Metric.ball p r := by
  intro z hz
  change Complex.normSq (z.1-p.1) + Complex.normSq (z.2-p.2) < r^2 at hz
  have h1 : ‖z.1-p.1‖ < r := by
    have hh := Complex.normSq_nonneg (z.2-p.2)
    rw [Complex.normSq_eq_norm_sq] at hz
    nlinarith [norm_nonneg (z.1-p.1)]
  have h2 : ‖z.2-p.2‖ < r := by
    have hh := Complex.normSq_nonneg (z.1-p.1)
    rw [Complex.normSq_eq_norm_sq] at hh
    change Complex.normSq (z.1-p.1) + Complex.normSq (z.2-p.2) < r^2 at hz
    rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq] at hz
    nlinarith [norm_nonneg (z.2-p.2)]
  simpa [Metric.mem_ball,dist_eq_norm,Prod.norm_def,max_lt_iff] using And.intro h1 h2

theorem CurvatureCurrent.small_ball_mass_finite {u : Coord → WithBot ℝ} {U : Set Coord}
    (T : CurvatureCurrent u U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r < δ →
      T.traceMeasure (euclideanBall p r) < ⊤ := by
  obtain ⟨δ,hδ,hsub⟩ := Metric.isOpen_iff.mp hU p hp
  refine ⟨δ/2,by linarith,?_⟩
  intro r hr hrδ
  apply lt_of_le_of_lt (measure_mono ((euclideanBall_subset_ball p r hr).trans
    (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hrδ.le))))
  apply T.trace_finite_compact _ (isCompact_closedBall p (δ/2))
  exact (Metric.closedBall_subset_ball (by linarith : δ/2 < δ)).trans hsub

/-- Nondegeneracy on every open component, expressed without a connectedness
assumption: finite points of the weight are relatively dense in its domain. -/
def FinitePointsDense (u : Coord → WithBot ℝ) (U : Set Coord) : Prop :=
  ∀ V : Set Coord, IsOpen V → V ⊆ U → V.Nonempty → ∃ x ∈ V, u x ≠ ⊥

/-- The standard psh-to-current and Lelong growth characterization, in the
paper's doubled-weight normalization and the actual Euclidean trace measure. -/
def PshCurrentStatement : Prop :=
  ∀ (u : Coord → WithBot ℝ) (U : Set Coord), IsOpen U →
    FailureOfSemipositiveMetricExtension.PlurisubharmonicOn u U → FinitePointsDense u U →
    ∃ T : CurvatureCurrent u U, ∀ p ∈ U,
      HasLelongNumber T p (FailureOfSemipositiveMetricExtension.logarithmicOrder u p)

end
end FailureOfSemipositiveMetricExtension.PshCurvatureCurrentInterface
