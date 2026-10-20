import FailureOfSemipositiveMetricExtension.BlowupSections
import FailureOfSemipositiveMetricExtension.Coordinates

/-! The paper's nearby pencil as actual coherent holomorphic section data on
all eight local blow-up charts. This file does not identify the local bundle
with a globally glued projective line bundle. -/
namespace FailureOfSemipositiveMetricExtension.PencilSections
noncomputable section
open FailureOfSemipositiveMetricExtension.Blowup FailureOfSemipositiveMetricExtension.BlowupSections

-- The first three centres have affine coordinates (y,z), (x,z), (y-1,z-t).
-- At the fourth centre the coordinates are (x,y).
def x₁ (t r s : ℂ) : Fin 2 → ℂ := ![s-t, -t+r*s]
def y₁ (t r s : ℂ) : Fin 2 → ℂ := ![1-t*s, -t*s+r*s]
def x₂ (t r s : ℂ) : Fin 2 → ℂ := ![-t+r*s, s-t]
def y₂ (t r s : ℂ) : Fin 2 → ℂ := ![-t*s+r*s, 1-t*s]
def x₃ (t r s : ℂ) : Fin 2 → ℂ := ![s-t, (1+r)*s]
def y₃ (t r s : ℂ) : Fin 2 → ℂ := ![1-t*s, 1+r*s]
def x₄ (t r s : ℂ) : Fin 2 → ℂ := ![1-t*r*s, s-t*r*s]
def y₄ (t r s : ℂ) : Fin 2 → ℂ := ![s-t*r*s, 1-t*r*s]

theorem coefficient_transitions (t r s : ℂ) (hs : s ≠ 0) (i : Fin 2) :
    x₁ t r s i = s * y₁ t (r*s) s⁻¹ i ∧
    x₂ t r s i = s * y₂ t (r*s) s⁻¹ i ∧
    x₃ t r s i = s * y₃ t (r*s) s⁻¹ i ∧
    x₄ t r s i = s * y₄ t (r*s) s⁻¹ i := by
  fin_cases i <;> simp [x₁,y₁,x₂,y₂,x₃,y₃,x₄,y₄]
  all_goals repeat' constructor
  all_goals field_simp [hs]
  all_goals ring

def pencilSystem₁ (t : ℂ) (i : Fin 2) : SectionData 1 where
  x q := x₁ t q.1 q.2 i
  y q := y₁ t q.1 q.2 i
  x_holomorphic := by fin_cases i <;> dsimp [x₁] <;> fun_prop
  y_holomorphic := by fin_cases i <;> dsimp [y₁] <;> fun_prop
  compatible r s hs := by simpa [transition] using (coefficient_transitions t r s hs i).1

def pencilSystem₂ (t : ℂ) (i : Fin 2) : SectionData 1 where
  x q := x₂ t q.1 q.2 i
  y q := y₂ t q.1 q.2 i
  x_holomorphic := by fin_cases i <;> dsimp [x₂] <;> fun_prop
  y_holomorphic := by fin_cases i <;> dsimp [y₂] <;> fun_prop
  compatible r s hs := by simpa [transition] using (coefficient_transitions t r s hs i).2.1

def pencilSystem₃ (t : ℂ) (i : Fin 2) : SectionData 1 where
  x q := x₃ t q.1 q.2 i
  y q := y₃ t q.1 q.2 i
  x_holomorphic := by fin_cases i <;> dsimp [x₃] <;> fun_prop
  y_holomorphic := by fin_cases i <;> dsimp [y₃] <;> fun_prop
  compatible r s hs := by simpa [transition] using (coefficient_transitions t r s hs i).2.2.1

def pencilSystem₄ (t : ℂ) (i : Fin 2) : SectionData 1 where
  x q := x₄ t q.1 q.2 i
  y q := y₄ t q.1 q.2 i
  x_holomorphic := by fin_cases i <;> dsimp [x₄] <;> fun_prop
  y_holomorphic := by fin_cases i <;> dsimp [y₄] <;> fun_prop
  compatible r s hs := by simpa [transition] using (coefficient_transitions t r s hs i).2.2.2

/-- Each nearby pencil has no common zero on the actual exceptional fibre. -/
theorem nearby_systems_no_exceptional_basepoint (t : ℂ) (ht : t ≠ 0)
    (p : Point) (hp : projection p = 0) :
    (∃ i, ¬ (pencilSystem₁ t i).zeroAt p) ∧
    (∃ i, ¬ (pencilSystem₂ t i).zeroAt p) ∧
    (∃ i, ¬ (pencilSystem₃ t i).zeroAt p) ∧
    (∃ i, ¬ (pencilSystem₄ t i).zeroAt p) := by
  rcases charts_cover p with ⟨r,s,rfl⟩ | ⟨r,s,rfl⟩
  · have hr := (projection_X_eq_zero_iff r s).mp hp
    subst r
    refine ⟨⟨1,?_⟩,⟨0,?_⟩,?_,⟨0,?_⟩⟩
    · simpa [zeroAt_X_iff,pencilSystem₁,x₁] using ht
    · simpa [zeroAt_X_iff,pencilSystem₂,x₂] using ht
    · by_cases hs : s = 0
      · exact ⟨0, by simpa [zeroAt_X_iff,pencilSystem₃,x₃,hs] using ht⟩
      · exact ⟨1, by simpa [zeroAt_X_iff,pencilSystem₃,x₃] using hs⟩
    · simp [zeroAt_X_iff,pencilSystem₄,x₄]
  · have hr := (projection_Y_eq_zero_iff r s).mp hp
    subst r
    refine ⟨?_,?_,⟨1,?_⟩,⟨1,?_⟩⟩
    · by_cases hs : s = 0
      · exact ⟨0, by simp [zeroAt_Y_iff,pencilSystem₁,y₁,hs]⟩
      · exact ⟨1, by simpa [zeroAt_Y_iff,pencilSystem₁,y₁] using mul_ne_zero (neg_ne_zero.mpr ht) hs⟩
    · by_cases hs : s = 0
      · exact ⟨1, by simp [zeroAt_Y_iff,pencilSystem₂,y₂,hs]⟩
      · exact ⟨0, by simpa [zeroAt_Y_iff,pencilSystem₂,y₂] using mul_ne_zero (neg_ne_zero.mpr ht) hs⟩
    · simp [zeroAt_Y_iff,pencilSystem₃,y₃]
    · simp [zeroAt_Y_iff,pencilSystem₄,y₄]

def homogeneousPencil (t x y z : ℂ) : Fin 2 → ℂ :=
  ![FailureOfSemipositiveMetricExtension.Coordinates.F₁ t x y z, FailureOfSemipositiveMetricExtension.Coordinates.F₂ t x y z]

/-- All local coefficient vectors are exactly the original two quadratic
polynomials pulled back and divided by the exceptional coordinate. -/
theorem all_pencil_divided_pullbacks (t r s : ℂ) :
    homogeneousPencil t 1 r (r*s) = r • x₁ t r s ∧
    homogeneousPencil t 1 (r*s) r = r • y₁ t r s ∧
    homogeneousPencil t r 1 (r*s) = r • x₂ t r s ∧
    homogeneousPencil t (r*s) 1 r = r • y₂ t r s ∧
    homogeneousPencil t 1 (1+r) (t+r*s) = r • x₃ t r s ∧
    homogeneousPencil t 1 (1+r*s) (t+r) = r • y₃ t r s ∧
    homogeneousPencil t r (r*s) 1 = r • x₄ t r s ∧
    homogeneousPencil t (r*s) r 1 = r • y₄ t r s := by
  repeat' constructor
  all_goals ext i; fin_cases i <;>
    simp [homogeneousPencil,FailureOfSemipositiveMetricExtension.Coordinates.F₁,FailureOfSemipositiveMetricExtension.Coordinates.F₂,
      x₁,y₁,x₂,y₂,x₃,y₃,x₄,y₄] <;> ring <;> simp
end
end FailureOfSemipositiveMetricExtension.PencilSections
