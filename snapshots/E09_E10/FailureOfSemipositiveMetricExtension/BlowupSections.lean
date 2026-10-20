import FailureOfSemipositiveMetricExtension.BlowupCharts
import FailureOfSemipositiveMetricExtension.Cubics

/-!
Explicit holomorphic section transition data on the actual two affine blow-up
charts. The transition `s^k` is derived from the exceptional local equations
`r_Y = r_X*s`. A global projective line bundle is not asserted in this file.
-/
namespace FailureOfSemipositiveMetricExtension.BlowupSections
noncomputable section
open FailureOfSemipositiveMetricExtension.Blowup

/-- Coherent local coefficients for the k-th exceptional vanishing twist.
The two local frames have relation e_Y = s^k e_X on the overlap. -/
structure SectionData (k : ℕ) where
  x : ℂ × ℂ → ℂ
  y : ℂ × ℂ → ℂ
  x_holomorphic : Differentiable ℂ x
  y_holomorphic : Differentiable ℂ y
  compatible : ∀ r s, s ≠ 0 → x (r,s) = s^k * y (transition (r,s))

/-- Zero of the coherent local section, stated invariantly over actual blow-up points. -/
def SectionData.zeroAt {k : ℕ} (a : SectionData k) (p : Point) : Prop :=
  (∀ r s, X r s = p → a.x (r,s) = 0) ∧
  (∀ r s, Y r s = p → a.y (r,s) = 0)

theorem zeroAt_X_iff {k : ℕ} (a : SectionData k) (r s : ℂ) :
    a.zeroAt (X r s) ↔ a.x (r,s) = 0 := by
  constructor
  · exact fun h => h.1 r s rfl
  · intro hx
    constructor
    · intro u v h
      have hpair : (u,v) = (r,s) := X_injective h
      simpa only [hpair] using hx
    · intro u v h
      have hcoords := (X_eq_Y_iff r s u v).mp h.symm
      have hs : s ≠ 0 := by
        intro hs; simp [hs] at hcoords
      have hv : v = s⁻¹ := by
        apply mul_left_cancel₀ hs
        rw [hcoords.2, mul_inv_cancel₀ hs]
      have ht : transition (r,s) = (u,v) := by
        simp [transition,hcoords.1,hv]
      have hc := a.compatible r s hs
      rw [hx,ht] at hc
      exact (mul_eq_zero.mp hc.symm).resolve_left (pow_ne_zero _ hs)

theorem zeroAt_Y_iff {k : ℕ} (a : SectionData k) (r s : ℂ) :
    a.zeroAt (Y r s) ↔ a.y (r,s) = 0 := by
  constructor
  · exact fun h => h.2 r s rfl
  · intro hy
    constructor
    · intro u v h
      have hcoords := (X_eq_Y_iff u v r s).mp h
      have hv : v ≠ 0 := by
        intro hv; simp [hv] at hcoords
      have hs : s = v⁻¹ := by
        apply mul_left_cancel₀ hv
        rw [hcoords.2, mul_inv_cancel₀ hv]
      have ht : transition (u,v) = (r,s) := by simp [transition,hcoords.1,hs]
      rw [a.compatible u v hv,ht,hy,mul_zero]
    · intro u v h
      have hpair : (u,v) = (r,s) := Y_injective h
      simpa only [hpair] using hy

-- Divided pullback coefficient vectors at the four central centres.
def x₁ (r s : ℂ) : Fin 4 → ℂ := ![s, r*s, r^2*s, 1-r]
def y₁ (r s : ℂ) : Fin 4 → ℂ := ![1, r*s, r^2*s^2, s-r*s^2]
def x₂ (r s : ℂ) : Fin 4 → ℂ := ![r^2*s, r*s, s, r-1]
def y₂ (r s : ℂ) : Fin 4 → ℂ := ![r^2*s^2, r*s, 1, r*s^2-s]
def x₃ (r s : ℂ) : Fin 4 → ℂ := ![s, (1+r)*s, (1+r)^2*s, -1-r]
def y₃ (r s : ℂ) : Fin 4 → ℂ := ![1, 1+r*s, (1+r*s)^2, -s-r*s^2]
def x₄ (r s : ℂ) : Fin 4 → ℂ := ![1, s, s^2, r*s*(1-s)]
def y₄ (r s : ℂ) : Fin 4 → ℂ := ![s^2, s, 1, r*s*(s-1)]

theorem coefficient_transitions (r s : ℂ) (hs : s ≠ 0) (i : Fin 4) :
    x₁ r s i = s * y₁ (r*s) s⁻¹ i ∧
    x₂ r s i = s * y₂ (r*s) s⁻¹ i ∧
    x₃ r s i = s * y₃ (r*s) s⁻¹ i ∧
    x₄ r s i = s^2 * y₄ (r*s) s⁻¹ i := by
  fin_cases i <;> simp [x₁,y₁,x₂,y₂,x₃,y₃,x₄,y₄]
  all_goals repeat' constructor
  all_goals field_simp [hs]
  all_goals ring

def cubicSystem₁ (i : Fin 4) : SectionData 1 where
  x q := x₁ q.1 q.2 i
  y q := y₁ q.1 q.2 i
  x_holomorphic := by fin_cases i <;> dsimp [x₁] <;> fun_prop
  y_holomorphic := by fin_cases i <;> dsimp [y₁] <;> fun_prop
  compatible r s hs := by simpa [transition] using (coefficient_transitions r s hs i).1

def cubicSystem₂ (i : Fin 4) : SectionData 1 where
  x q := x₂ q.1 q.2 i
  y q := y₂ q.1 q.2 i
  x_holomorphic := by fin_cases i <;> dsimp [x₂] <;> fun_prop
  y_holomorphic := by fin_cases i <;> dsimp [y₂] <;> fun_prop
  compatible r s hs := by simpa [transition] using (coefficient_transitions r s hs i).2.1

def cubicSystem₃ (i : Fin 4) : SectionData 1 where
  x q := x₃ q.1 q.2 i
  y q := y₃ q.1 q.2 i
  x_holomorphic := by fin_cases i <;> dsimp [x₃] <;> fun_prop
  y_holomorphic := by fin_cases i <;> dsimp [y₃] <;> fun_prop
  compatible r s hs := by simpa [transition] using (coefficient_transitions r s hs i).2.2.1

def cubicSystem₄ (i : Fin 4) : SectionData 2 where
  x q := x₄ q.1 q.2 i
  y q := y₄ q.1 q.2 i
  x_holomorphic := by fin_cases i <;> dsimp [x₄] <;> fun_prop
  y_holomorphic := by fin_cases i <;> dsimp [y₄] <;> fun_prop
  compatible r s hs := by simpa [transition] using (coefficient_transitions r s hs i).2.2.2

/-- All four central systems have no common zero on the actual exceptional fibre. -/
theorem central_systems_no_exceptional_basepoint (p : Point) (hp : projection p = 0) :
    (∃ i, ¬ (cubicSystem₁ i).zeroAt p) ∧
    (∃ i, ¬ (cubicSystem₂ i).zeroAt p) ∧
    (∃ i, ¬ (cubicSystem₃ i).zeroAt p) ∧
    (∃ i, ¬ (cubicSystem₄ i).zeroAt p) := by
  rcases charts_cover p with ⟨r,s,rfl⟩ | ⟨r,s,rfl⟩
  · have hr := (projection_X_eq_zero_iff r s).mp hp
    subst r
    refine ⟨⟨3,?_⟩,⟨3,?_⟩,⟨3,?_⟩,⟨0,?_⟩⟩ <;>
      rw [zeroAt_X_iff] <;>
      norm_num [cubicSystem₁,cubicSystem₂,cubicSystem₃,cubicSystem₄,x₁,x₂,x₃,x₄,
        Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail]
  · have hr := (projection_Y_eq_zero_iff r s).mp hp
    subst r
    refine ⟨⟨0,?_⟩,⟨2,?_⟩,⟨0,?_⟩,⟨2,?_⟩⟩ <;>
      rw [zeroAt_Y_iff] <;>
      norm_num [cubicSystem₁,cubicSystem₂,cubicSystem₃,cubicSystem₄,y₁,y₂,y₃,y₄,
        Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]

/-- The paper's ordered tuple of homogeneous cubic generators. -/
def homogeneousCubics (x y z : ℂ) : Fin 4 → ℂ := ![x^2*z, x*y*z, y^2*z, x*y*(x-y)]

/-- Exact identities relating all divided local section coefficients to the
original homogeneous cubics. They hold on the exceptional locus as polynomial identities. -/
theorem all_cubic_divided_pullbacks (r s : ℂ) :
    homogeneousCubics 1 r (r*s) = r • x₁ r s ∧
    homogeneousCubics 1 (r*s) r = r • y₁ r s ∧
    homogeneousCubics r 1 (r*s) = r • x₂ r s ∧
    homogeneousCubics (r*s) 1 r = r • y₂ r s ∧
    homogeneousCubics 1 (1+r) (r*s) = r • x₃ r s ∧
    homogeneousCubics 1 (1+r*s) r = r • y₃ r s ∧
    homogeneousCubics r (r*s) 1 = r^2 • x₄ r s ∧
    homogeneousCubics (r*s) r 1 = r^2 • y₄ r s := by
  repeat' constructor
  all_goals ext i; fin_cases i <;>
    simp [homogeneousCubics,x₁,y₁,x₂,y₂,x₃,y₃,x₄,y₄] <;> ring
end
end FailureOfSemipositiveMetricExtension.BlowupSections
