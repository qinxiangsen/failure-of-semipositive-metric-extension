import Mathlib.Tactic

/-! Explicit homogeneous coordinates and polynomial equations, over ℂ.
No assertion of a geometric blow-up or line-bundle correspondence is implicit. -/
namespace FailureOfSemipositiveMetricExtension.Coordinates
abbrev Point := Fin 3 → ℂ
def p₁ : Point := ![1, 0, 0]
def p₂ : Point := ![0, 1, 0]
def p₃ (t : ℂ) : Point := ![1, 1, t]
def p₄ : Point := ![0, 0, 1]
def F₁ (t x y z : ℂ) := x * (z - t * y)
def F₂ (t x y z : ℂ) := y * (z - t * x)
def det (a b c : Point) :=
  a 0 * (b 1 * c 2 - b 2 * c 1) -
  a 1 * (b 0 * c 2 - b 2 * c 0) +
  a 2 * (b 0 * c 1 - b 1 * c 0)

theorem quadrics_vanish (t : ℂ) :
    F₁ t 1 0 0 = 0 ∧ F₂ t 1 0 0 = 0 ∧
    F₁ t 0 1 0 = 0 ∧ F₂ t 0 1 0 = 0 ∧
    F₁ t 1 1 t = 0 ∧ F₂ t 1 1 t = 0 ∧
    F₁ t 0 0 1 = 0 ∧ F₂ t 0 0 1 = 0 := by simp [F₁, F₂]

theorem determinants (t : ℂ) :
    det p₁ p₂ (p₃ t) = t ∧ det p₁ p₂ p₄ = 1 ∧
    det p₁ (p₃ t) p₄ = 1 ∧ det p₂ (p₃ t) p₄ = -1 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, det, p₁, p₂, p₃, p₄]

theorem no_three_collinear_determinants (t : ℂ) (ht : t ≠ 0) :
    det p₁ p₂ (p₃ t) ≠ 0 ∧ det p₁ p₂ p₄ ≠ 0 ∧
    det p₁ (p₃ t) p₄ ≠ 0 ∧ det p₂ (p₃ t) p₄ ≠ 0 := by
  simpa [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, det, p₁, p₂, p₃, p₄] using ht

theorem central_collinearity : det p₁ p₂ (p₃ 0) = 0 := by
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail, det, p₁, p₂, p₃]

/-- The affine cone over the common zero locus is exactly the four indicated lines. -/
theorem nearby_common_zero_locus (t x y z : ℂ) (ht : t ≠ 0) :
    (F₁ t x y z = 0 ∧ F₂ t x y z = 0) ↔
    (x = 0 ∧ y = 0) ∨ (y = 0 ∧ z = 0) ∨
    (x = 0 ∧ z = 0) ∨ (x = y ∧ z = t * x) := by
  constructor
  · rintro ⟨h₁, h₂⟩
    rcases mul_eq_zero.mp h₁ with hx | hz₁
    · rcases mul_eq_zero.mp h₂ with hy | hz₂
      · exact Or.inl ⟨hx, hy⟩
      · exact Or.inr (Or.inr (Or.inl ⟨hx, by simpa [hx] using hz₂⟩))
    · rcases mul_eq_zero.mp h₂ with hy | hz₂
      · exact Or.inr (Or.inl ⟨hy, by simpa [hy] using hz₁⟩)
      · have hz₁' : z = t * y := sub_eq_zero.mp hz₁
        have hz₂' : z = t * x := sub_eq_zero.mp hz₂
        have hxy : x = y := mul_left_cancel₀ ht (hz₂'.symm.trans hz₁')
        exact Or.inr (Or.inr (Or.inr ⟨hxy, hz₂'⟩))
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      simp [F₁, F₂]

/-- Exact centered chart expansions, including the higher-order terms. -/
theorem nearby_chart_expansions (t u v : ℂ) :
    (F₁ t 1 u v = v - t * u) ∧
    (F₂ t 1 u v = -t * u + u * v) ∧
    (F₁ t u 1 v = -t * u + u * v) ∧
    (F₂ t u 1 v = v - t * u) ∧
    (F₁ t 1 (1 + u) (t + v) = v - t * u) ∧
    (F₂ t 1 (1 + u) (t + v) = v + u * v) ∧
    (F₁ t u v 1 = u - t * u * v) ∧
    (F₂ t u v 1 = v - t * u * v) := by
  dsimp [F₁, F₂]
  repeat' constructor
  all_goals ring

/-- The four displayed linear initial-term pairs have no nonzero common zero. -/
theorem nearby_initial_terms (t u v : ℂ) (ht : t ≠ 0) :
    ((v - t*u = 0 ∧ -t*u = 0) → u = 0 ∧ v = 0) ∧
    ((-t*u = 0 ∧ v-t*u = 0) → u = 0 ∧ v = 0) ∧
    ((v-t*u = 0 ∧ v = 0) → u = 0 ∧ v = 0) ∧
    ((u = 0 ∧ v = 0) → u = 0 ∧ v = 0) := by
  have hmul : ∀ w : ℂ, -t*w = 0 → w = 0 := by
    intro w h; exact (mul_eq_zero.mp h).resolve_left (neg_ne_zero.mpr ht)
  refine ⟨?_, ?_, ?_, id⟩
  · rintro ⟨h₁,h₂⟩; have hu := hmul u h₂; exact ⟨hu, by simpa [hu] using h₁⟩
  · rintro ⟨h₁,h₂⟩; have hu := hmul u h₁; exact ⟨hu, by simpa [hu] using h₂⟩
  · rintro ⟨h₁,h₂⟩; subst v
    exact ⟨hmul u (by simpa using h₁), rfl⟩
end FailureOfSemipositiveMetricExtension.Coordinates
