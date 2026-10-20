import Mathlib.Tactic

namespace FailureOfSemipositiveMetricExtension.Cubics
structure Cubic where
  xxx : ℂ
  xxy : ℂ
  xyy : ℂ
  yyy : ℂ
  xxz : ℂ
  xyz : ℂ
  yyz : ℂ
  xzz : ℂ
  yzz : ℂ
  zzz : ℂ

def Cubic.eval (c : Cubic) (x y z : ℂ) :=
  c.xxx*x^3 + c.xxy*x^2*y + c.xyy*x*y^2 + c.yyy*y^3 +
  c.xxz*x^2*z + c.xyz*x*y*z + c.yyz*y^2*z +
  c.xzz*x*z^2 + c.yzz*y*z^2 + c.zzz*z^3

/-- Explicit constant and linear Taylor coefficients in the chart z=1 vanish. -/
def Cubic.doubleAtP4 (c : Cubic) : Prop := c.zzz = 0 ∧ c.xzz = 0 ∧ c.yzz = 0

theorem cubic_span (c : Cubic)
    (h₁ : c.eval 1 0 0 = 0) (h₂ : c.eval 0 1 0 = 0)
    (h₃ : c.eval 1 1 0 = 0) (h₄ : c.doubleAtP4) :
    ∀ x y z : ℂ, c.eval x y z =
      c.xxz*(x^2*z) + c.xyz*(x*y*z) + c.yyz*(y^2*z) + c.xxy*(x*y*(x-y)) := by
  rcases h₄ with ⟨hzzz, hxzz, hyzz⟩
  simp only [Cubic.eval, one_pow, zero_pow (by decide : 3 ≠ 0),
    zero_pow (by decide : 2 ≠ 0), mul_one, mul_zero, zero_add, add_zero] at h₁ h₂ h₃
  have hxyy : c.xyy = -c.xxy := by linear_combination h₃ - h₁ - h₂
  intro x y z
  simp only [Cubic.eval, h₁, h₂, hxyy, hzzz, hxzz, hyzz]
  ring

def g₁ (x _y z : ℂ) := x^2*z
def g₂ (x y z : ℂ) := x*y*z
def g₃ (_x y z : ℂ) := y^2*z
def g₄ (x y _z : ℂ) := x*y*(x-y)

theorem generators_common_zero_locus (x y z : ℂ) :
    (g₁ x y z = 0 ∧ g₂ x y z = 0 ∧ g₃ x y z = 0 ∧ g₄ x y z = 0) ↔
    (x = 0 ∧ y = 0) ∨ (z = 0 ∧ y = 0) ∨
    (z = 0 ∧ x = 0) ∨ (z = 0 ∧ x = y) := by
  constructor
  · rintro ⟨h₁,h₂,h₃,h₄⟩
    by_cases hz : z = 0
    · rcases mul_eq_zero.mp h₄ with hxy | heq
      · rcases mul_eq_zero.mp hxy with hx | hy
        · exact Or.inr (Or.inr (Or.inl ⟨hz,hx⟩))
        · exact Or.inr (Or.inl ⟨hz,hy⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨hz,sub_eq_zero.mp heq⟩))
    · have hx : x^2 = 0 := (mul_eq_zero.mp h₁).resolve_right hz
      have hy : y^2 = 0 := (mul_eq_zero.mp h₃).resolve_right hz
      exact Or.inl ⟨pow_eq_zero hx, pow_eq_zero hy⟩
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;>
      simp [g₁,g₂,g₃,g₄]

theorem exceptional_quadratics_no_common_zero (u v : ℂ)
    (hu : u^2 = 0) (hv : v^2 = 0) : u = 0 ∧ v = 0 :=
  ⟨pow_eq_zero hu, pow_eq_zero hv⟩

theorem central_chart_expansions (u v : ℂ) :
    g₁ 1 u v = v ∧ g₄ 1 u v = u - u^2 ∧
    g₃ u 1 v = v ∧ g₄ u 1 v = -u + u^2 ∧
    g₁ 1 (1+u) v = v ∧ g₄ 1 (1+u) v = -u-u^2 ∧
    g₁ u v 1 = u^2 ∧ g₂ u v 1 = u*v ∧ g₃ u v 1 = v^2 := by
  dsimp [g₁,g₂,g₃,g₄]
  repeat' constructor
  all_goals ring

/-- The exact divided pullbacks in the two affine blow-up charts at each centre.
Each equation is polynomial, so division across the exceptional locus is justified
by the identity rather than by cancelling a value that might be zero. -/
theorem central_blowup_chart_identities (r s : ℂ) :
    g₁ 1 r (r*s) = r*s ∧ g₄ 1 r (r*s) = r*(1-r) ∧
    g₁ 1 (r*s) r = r*1 ∧
    g₃ r 1 (r*s) = r*s ∧ g₄ r 1 (r*s) = r*(r-1) ∧
    g₃ (r*s) 1 r = r*1 ∧
    g₁ 1 (1+r) (r*s) = r*s ∧ g₄ 1 (1+r) (r*s) = r*(-1-r) ∧
    g₁ 1 (1+r*s) r = r*1 ∧
    g₁ r (r*s) 1 = r^2*1 ∧
    g₂ r (r*s) 1 = r^2*s ∧
    g₃ r (r*s) 1 = r^2*s^2 ∧
    g₄ r (r*s) 1 = r^2*(r*s*(1-s)) ∧
    g₁ (r*s) r 1 = r^2*s^2 ∧
    g₂ (r*s) r 1 = r^2*s ∧
    g₃ (r*s) r 1 = r^2*1 ∧
    g₄ (r*s) r 1 = r^2*(r*s*(s-1)) := by
  dsimp [g₁,g₂,g₃,g₄]
  repeat' constructor
  all_goals ring

/-- At r=0, a displayed divided pullback is a nonzero constant in every chart. -/
theorem central_exceptional_chart_units :
    (1-(0:ℂ) ≠ 0) ∧ ((0:ℂ)-1 ≠ 0) ∧ (-(1:ℂ)-(0:ℂ) ≠ 0) ∧ ((1:ℂ) ≠ 0) := by
  norm_num

structure Conic where
  xx : ℂ
  xy : ℂ
  yy : ℂ
  xz : ℂ
  yz : ℂ
  zz : ℂ

def Conic.eval (c : Conic) (x y z : ℂ) :=
  c.xx*x^2 + c.xy*x*y + c.yy*y^2 + c.xz*x*z + c.yz*y*z + c.zz*z^2

def Conic.doubleAtP4 (c : Conic) : Prop := c.zz = 0 ∧ c.xz = 0 ∧ c.yz = 0

/-- Coefficient-level proof of the m=3 conic impossibility, without Bézout. -/
theorem conic_impossible (c : Conic)
    (h₁ : c.eval 1 0 0 = 0) (h₂ : c.eval 0 1 0 = 0)
    (h₃ : c.eval 1 1 0 = 0) (h₄ : c.doubleAtP4) :
    c.xx = 0 ∧ c.xy = 0 ∧ c.yy = 0 ∧ c.xz = 0 ∧ c.yz = 0 ∧ c.zz = 0 := by
  rcases h₄ with ⟨hzz,hxz,hyz⟩
  simp [Conic.eval] at h₁ h₂ h₃
  exact ⟨h₁, by linear_combination h₃ - h₁ - h₂, h₂, hxz, hyz, hzz⟩

theorem conic_eval_zero (c : Conic)
    (h₁ : c.eval 1 0 0 = 0) (h₂ : c.eval 0 1 0 = 0)
    (h₃ : c.eval 1 1 0 = 0) (h₄ : c.doubleAtP4) :
    ∀ x y z : ℂ, c.eval x y z = 0 := by
  rcases conic_impossible c h₁ h₂ h₃ h₄ with ⟨hxx,hxy,hyy,hxz,hyz,hzz⟩
  intro x y z
  simp [Conic.eval,hxx,hxy,hyy,hxz,hyz,hzz]
end FailureOfSemipositiveMetricExtension.Cubics
