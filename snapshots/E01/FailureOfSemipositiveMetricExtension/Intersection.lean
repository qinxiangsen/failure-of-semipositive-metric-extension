import Mathlib.Tactic

/-!
# Numerical divisor lattice of the four-point construction
These are identities in the explicit rational lattice with Gram matrix
`diag(1,-1,-1,-1,-1)`. The identification with the Picard/intersection lattice
of the geometric blow-up is NOT asserted by this module.
-/
namespace FailureOfSemipositiveMetricExtension
abbrev DivisorVector := Fin 5 → ℚ

def H : DivisorVector := ![1, 0, 0, 0, 0]
def E₁ : DivisorVector := ![0, 1, 0, 0, 0]
def E₂ : DivisorVector := ![0, 0, 1, 0, 0]
def E₃ : DivisorVector := ![0, 0, 0, 1, 0]
def E₄ : DivisorVector := ![0, 0, 0, 0, 1]
def L : DivisorVector := ![2, -1, -1, -1, -1]
def K : DivisorVector := ![-3, 1, 1, 1, 1]
def ell : DivisorVector := ![1, -1, -1, -1, 0]
def A : DivisorVector := ![3, -1, -1, -1, -2]
def Q : DivisorVector := ![3, -1, -1, -1, -3]
def q₁ : DivisorVector := ![1, -1, 0, 0, -1]
def q₂ : DivisorVector := ![1, 0, -1, 0, -1]
def q₃ : DivisorVector := ![1, 0, 0, -1, -1]

def intersection (d e : DivisorVector) : ℚ :=
  d 0 * e 0 - d 1 * e 1 - d 2 * e 2 - d 3 * e 3 - d 4 * e 4

theorem intersection_symmetric (d e : DivisorVector) :
    intersection d e = intersection e d := by unfold intersection; ring

theorem L_square : intersection L L = 0 := by norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, intersection, L]
theorem K_dot_L : intersection K L = -2 := by norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, intersection, K, L]
theorem ell_square : intersection ell ell = -2 := by norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, intersection, ell]
theorem A_dot_ell : intersection A ell = 0 := by norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, intersection, A, ell]
theorem L_dot_ell : intersection L ell = -1 := by norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, intersection, L, ell]
theorem A_square : intersection A A = 2 := by norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, intersection, A]

theorem A_definition : A = (2 : ℚ) • L - ell := by
  ext i; fin_cases i <;> norm_num [A, L, ell]
theorem Q_sum : Q = q₁ + q₂ + q₃ := by
  ext i; fin_cases i <;> norm_num [Q, q₁, q₂, q₃]
theorem Q_adjoint : Q = K + (4 : ℚ) • L - (2 : ℚ) • ell := by
  ext i; fin_cases i <;> norm_num [Q, K, L, ell]
theorem Q_two_A : Q = K + (2 : ℚ) • A := by
  ext i; fin_cases i <;> norm_num [Q, K, A]
theorem zariski_vector_identity : L = (1 / 2 : ℚ) • A + (1 / 2 : ℚ) • ell := by
  ext i; fin_cases i <;> norm_num [L, A, ell]

theorem adjoint_intersection (m : ℚ) : intersection (K + m • L) L = -2 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, intersection, K, L]; ring

theorem adjoint_intersection_negative (m : ℚ) :
    ¬ 0 ≤ intersection (K + m • L) L := by
  rw [adjoint_intersection]; norm_num

theorem negative_coefficient_unique (c : ℚ)
    (horthogonal : intersection (L - c • ell) ell = 0) : c = 1 / 2 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, intersection, L, ell] at horthogonal
  linarith

def integrableAdjointVector (m : ℕ) : DivisorVector :=
  K + (m : ℚ) • L - ((m / 2 : ℕ) : ℚ) • ell

theorem integrable_adjoint_one : integrableAdjointVector 1 = -H := by
  ext i; fin_cases i <;> norm_num [integrableAdjointVector, K, L, ell, H]
theorem integrable_adjoint_two : integrableAdjointVector 2 = -E₄ := by
  ext i; fin_cases i <;> norm_num [integrableAdjointVector, K, L, ell, E₄]
theorem integrable_adjoint_three :
    integrableAdjointVector 3 = ![2, -1, -1, -1, -2] := by
  ext i; fin_cases i <;> norm_num [integrableAdjointVector, K, L, ell]
theorem integrable_adjoint_four : integrableAdjointVector 4 = Q := by
  ext i; fin_cases i <;> norm_num [integrableAdjointVector, K, L, ell, Q]
theorem minus_H_degree : intersection (-H) H = -1 := by norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, intersection, H]

-- The numerical calculations in the discussion of Hisamoto Example 4.12.
def ruling : DivisorVector := H - E₁
def hisamotoBundle : DivisorVector := H + E₁
theorem ruling_square : intersection ruling ruling = 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, intersection, ruling, H, E₁]
theorem hisamoto_degree_two : intersection hisamotoBundle ruling = 2 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, intersection, hisamotoBundle, ruling, H, E₁]
end FailureOfSemipositiveMetricExtension
