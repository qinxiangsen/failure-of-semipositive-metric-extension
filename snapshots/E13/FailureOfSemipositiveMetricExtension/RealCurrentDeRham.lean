import FailureOfSemipositiveMetricExtension.DistributionalCurrentAtlas

/-! Genuine de Rham exactness of independently represented real (1,1)-currents.
The primitive is an arbitrary real distributional ONE-form with the actual
covector/density overlap law; it is not required to be d^c of a function. -/
namespace FailureOfSemipositiveMetricExtension.DistributionalCurrent
noncomputable section
open Set MeasureTheory
open WeakComplexHessian CurrentCoordinateCovariance PshCurvatureCurrentInterface
open scoped ContDiff

/-- The real coordinate basis (x0,y0,x1,y1). -/
def realUnit (i : Fin 4) : Coord := ![(1,0),(Complex.I,0),(0,1),(0,Complex.I)] i

def realComponent (i : Fin 4) (z : Coord) : ℝ := ![z.1.re,z.1.im,z.2.re,z.2.im] i

/-- Pullback of a covector coefficient, including inverse real volume density. -/
def transportedOneTest (e : PartialHomeomorph Coord Coord) (f : Coord → ℝ)
    (i r : Fin 4) (y : Coord) : ℝ := by
  classical
  exact if y ∈ e.target then f (e.symm y) * realComponent r (fderiv ℝ e (e.symm y) (realUnit i)) *
    Complex.normSq (ComplexSurfaceJacobian.jacobian e.symm y) else 0

/-- Standard finite-order distribution continuity on each compact test support.
The derivative order may depend on the compact support. -/
def FiniteDistributionOrder (F : (Coord → ℝ) → ℝ) (U : Set Coord) : Prop :=
  ∀ K, IsCompact K → K ⊆ U → ∃ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧
    ∀ f, IsTest U f → tsupport f ⊆ K → ∀ R : ℝ, 0 ≤ R →
      (∀ m ≤ n, ∀ x ∈ K, ‖iteratedFDeriv ℝ m f x‖ ≤ R) → ‖F f‖ ≤ B*R

variable {M A : Type} [TopologicalSpace M] [ChartedSpace Coord M]

/-- Arbitrary real distributional one-forms; coordinate descent is explicit. -/
structure OneCurrent (D : CoordinateAtlas M A) where
  coefficient : A → Fin 4 → (Coord → ℝ) → ℝ
  additive : ∀ a i f g, IsTest (D.coordinate a).chart.target f →
    IsTest (D.coordinate a).chart.target g → coefficient a i (f+g) = coefficient a i f + coefficient a i g
  homogeneous : ∀ a i f, IsTest (D.coordinate a).chart.target f → ∀ r : ℝ,
    coefficient a i (r • f) = r*coefficient a i f
  finiteOrder : ∀ a i, FiniteDistributionOrder (coefficient a i) (D.coordinate a).chart.target
  transported_test : ∀ a b f, IsTest (D.change a b).source f → ∀ i r,
    IsTest (D.change a b).target (transportedOneTest (D.change a b) f i r)
  compatible : ∀ a b f, IsTest (D.change a b).source f → ∀ i,
    coefficient a i f = ∑ r : Fin 4, coefficient b r (transportedOneTest (D.change a b) f i r)

/-- Real two-form coefficient of i Σ C[j,k] dz[j]∧dbarz[k]. This fixes all
mixed imaginary signs and the paper's i/(2π) ddbar convention. -/
def realTwoCoefficient (C : CoefficientField A) (a : A) (i l : Fin 4) (f : Coord → ℝ) : ℝ :=
  (Complex.I * ∑ j : Fin 2, ∑ k : Fin 2,
    (component j (realUnit i) * star (component k (realUnit l)) -
      component j (realUnit l) * star (component k (realUnit i))) * C a j k f).re

/-- Exterior derivative of the actual one-current, with distributional
integration-by-parts signs: (dα)[i,l] = ∂i α[l] − ∂l α[i]. -/
def OneCurrent.exteriorCoefficient {D : CoordinateAtlas M A} (R : OneCurrent D)
    (a : A) (i l : Fin 4) (f : Coord → ℝ) : ℝ :=
  -R.coefficient a l (firstDirectional (realUnit i) f) +
    R.coefficient a i (firstDirectional (realUnit l) f)

/-- A true de Rham primitive of T−S. The primitive is NOT a potential function,
so any dd^c conclusion from this hypothesis needs a separate Kähler theorem. -/
def DeRhamExactEquivalent (D : CoordinateAtlas M A) (T S : Current D) : Prop :=
  ∃ R : OneCurrent D, ∀ a f, IsTest (D.coordinate a).chart.target f → ∀ i l,
    realTwoCoefficient T.coefficient a i l f - realTwoCoefficient S.coefficient a i l f =
      R.exteriorCoefficient a i l f

@[simp] theorem realTwoCoefficient_xy0 (C : CoefficientField A) (a : A) (f : Coord → ℝ) :
    realTwoCoefficient C a 0 1 f = 2 * (C a 0 0 f).re := by
  simp [realTwoCoefficient,Fin.sum_univ_two,component,realUnit,Complex.mul_re,Complex.mul_im]
  ring

@[simp] theorem realTwoCoefficient_xy1 (C : CoefficientField A) (a : A) (f : Coord → ℝ) :
    realTwoCoefficient C a 2 3 f = 2 * (C a 1 1 f).re := by
  simp [realTwoCoefficient,Fin.sum_univ_two,component,realUnit,Complex.mul_re,Complex.mul_im]
  ring

end
end FailureOfSemipositiveMetricExtension.DistributionalCurrent
