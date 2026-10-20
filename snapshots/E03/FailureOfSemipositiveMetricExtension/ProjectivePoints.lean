import FailureOfSemipositiveMetricExtension.Coordinates
import FailureOfSemipositiveMetricExtension.Cubics
import Mathlib.LinearAlgebra.Projectivization.Basic

namespace FailureOfSemipositiveMetricExtension.Coordinates

private theorem first_coordinate_nonzero (v : Point) (h : v 0 = 1) : v ≠ 0 := by
  intro hv
  have hc := congrFun hv 0
  simp only [Pi.zero_apply, h] at hc
  exact one_ne_zero hc

 theorem p₁_nonzero : p₁ ≠ 0 := first_coordinate_nonzero p₁ rfl
 theorem p₂_nonzero : p₂ ≠ 0 := by
  intro h; have hc := congrFun h 1; norm_num [p₂] at hc
 theorem p₃_nonzero (t : ℂ) : p₃ t ≠ 0 := first_coordinate_nonzero (p₃ t) rfl
 theorem p₄_nonzero : p₄ ≠ 0 := by
  intro h; have hc := congrFun h 2
  norm_num [p₄, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] at hc

noncomputable def P₁ := Projectivization.mk ℂ p₁ p₁_nonzero
noncomputable def P₂ := Projectivization.mk ℂ p₂ p₂_nonzero
noncomputable def P₃ (t : ℂ) := Projectivization.mk ℂ (p₃ t) (p₃_nonzero t)
noncomputable def P₄ := Projectivization.mk ℂ p₄ p₄_nonzero

/-- Pairwise distinctness is in mathlib's actual projective quotient, not just
inequality of the chosen homogeneous vectors. -/
theorem four_projective_points_distinct (t : ℂ) :
    P₁ ≠ P₂ ∧ P₁ ≠ P₃ t ∧ P₁ ≠ P₄ ∧
    P₂ ≠ P₃ t ∧ P₂ ≠ P₄ ∧ P₃ t ≠ P₄ := by
  have hn : ∀ (v w : Point) (hv : v ≠ 0) (hw : w ≠ 0),
      (∀ a : ℂ, a • w ≠ v) → Projectivization.mk ℂ v hv ≠ Projectivization.mk ℂ w hw := by
    intro v w hv hw hneq heq
    rcases (Projectivization.mk_eq_mk_iff' ℂ v w hv hw).mp heq with ⟨a,ha⟩
    exact hneq a ha
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply hn; intro a ha
    have h := congrFun ha 0; norm_num [p₁,p₂] at h
  · apply hn; intro a ha
    have h₀ := congrFun ha 0; have h₁ := congrFun ha 1
    simp [p₁,p₃] at h₀ h₁
    exact zero_ne_one (h₁.symm.trans h₀)
  · apply hn; intro a ha
    have h := congrFun ha 0; norm_num [p₁,p₄] at h
  · apply hn; intro a ha
    have h₀ := congrFun ha 0; have h₁ := congrFun ha 1
    simp [p₂,p₃] at h₀ h₁
    exact zero_ne_one (h₀.symm.trans h₁)
  · apply hn; intro a ha
    have h := congrFun ha 1; norm_num [p₂,p₄] at h
  · apply hn; intro a ha
    have h := congrFun ha 0; norm_num [p₃,p₄] at h

/-- A nonzero linear equation cannot contain the first three points when t≠0. -/
theorem no_linear_equation_nearby_123 (t a b c : ℂ) (ht : t ≠ 0)
    (h₁ : a = 0) (h₂ : b = 0) (h₃ : a + b + c*t = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  refine ⟨h₁,h₂,?_⟩
  have hct : c*t = 0 := by simpa [h₁,h₂] using h₃
  exact (mul_eq_zero.mp hct).resolve_right ht

theorem no_linear_equation_124 (a b c : ℂ)
    (h₁ : a = 0) (h₂ : b = 0) (h₄ : c = 0) : a = 0 ∧ b = 0 ∧ c = 0 := ⟨h₁,h₂,h₄⟩
theorem no_linear_equation_134 (t a b c : ℂ)
    (h₁ : a = 0) (h₃ : a+b+c*t = 0) (h₄ : c = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  exact ⟨h₁, by simpa [h₁,h₄] using h₃, h₄⟩
theorem no_linear_equation_234 (t a b c : ℂ)
    (h₂ : b = 0) (h₃ : a+b+c*t = 0) (h₄ : c = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  exact ⟨by simpa [h₂,h₄] using h₃, h₂, h₄⟩

/-- The common projective zero locus of the nearby pencil consists of exactly
the four specified projective points. -/
theorem projective_common_zero_locus (t : ℂ) (ht : t ≠ 0) (v : Point) (hv : v ≠ 0) :
    (F₁ t (v 0) (v 1) (v 2) = 0 ∧ F₂ t (v 0) (v 1) (v 2) = 0) ↔
    (Projectivization.mk ℂ v hv = P₁ ∨ Projectivization.mk ℂ v hv = P₂ ∨
     Projectivization.mk ℂ v hv = P₃ t ∨ Projectivization.mk ℂ v hv = P₄) := by
  constructor
  · intro h
    rcases (nearby_common_zero_locus t (v 0) (v 1) (v 2) ht).mp h with
      h₄ | h₁ | h₂ | h₃
    · apply Or.inr; apply Or.inr; apply Or.inr
      apply (Projectivization.mk_eq_mk_iff' ℂ v p₄ hv p₄_nonzero).mpr
      refine ⟨v 2, ?_⟩
      ext i; fin_cases i <;> simp [p₄, h₄.1, h₄.2]
    · apply Or.inl
      apply (Projectivization.mk_eq_mk_iff' ℂ v p₁ hv p₁_nonzero).mpr
      refine ⟨v 0, ?_⟩
      ext i; fin_cases i <;> simp [p₁, h₁.1, h₁.2]
    · apply Or.inr; apply Or.inl
      apply (Projectivization.mk_eq_mk_iff' ℂ v p₂ hv p₂_nonzero).mpr
      refine ⟨v 1, ?_⟩
      ext i; fin_cases i <;> simp [p₂, h₂.1, h₂.2]
    · apply Or.inr; apply Or.inr; apply Or.inl
      apply (Projectivization.mk_eq_mk_iff' ℂ v (p₃ t) hv (p₃_nonzero t)).mpr
      refine ⟨v 0, ?_⟩
      ext i; fin_cases i <;> simp [p₃, h₃.1, h₃.2, mul_comm]
  · rintro (h | h | h | h)
    · rcases (Projectivization.mk_eq_mk_iff' ℂ v p₁ hv p₁_nonzero).mp h with ⟨a,ha⟩
      rw [← ha]; simp [F₁,F₂,p₁,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
    · rcases (Projectivization.mk_eq_mk_iff' ℂ v p₂ hv p₂_nonzero).mp h with ⟨a,ha⟩
      rw [← ha]; simp [F₁,F₂,p₂,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
    · rcases (Projectivization.mk_eq_mk_iff' ℂ v (p₃ t) hv (p₃_nonzero t)).mp h with ⟨a,ha⟩
      rw [← ha]; simp [F₁,F₂,p₃,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,mul_comm]
    · rcases (Projectivization.mk_eq_mk_iff' ℂ v p₄ hv p₄_nonzero).mp h with ⟨a,ha⟩
      rw [← ha]; simp [F₁,F₂,p₄,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]

/-- The graphs of pointwise distinct maps are disjoint subsets of a product. -/
theorem disjoint_graphs_of_pointwise_ne {B Y : Type*} (f g : B → Y)
    (hne : ∀ b, f b ≠ g b) :
    Disjoint (Set.range fun b => (f b, b)) (Set.range fun b => (g b, b)) := by
  rw [Set.disjoint_left]
  rintro p ⟨b,rfl⟩ ⟨c,hc⟩
  have hbc : c = b := congrArg Prod.snd hc
  subst c
  exact hne b (congrArg Prod.fst hc).symm

theorem four_section_graphs_disjoint :
    Disjoint (Set.range fun t : ℂ => (P₁,t)) (Set.range fun t : ℂ => (P₂,t)) ∧
    Disjoint (Set.range fun t : ℂ => (P₁,t)) (Set.range fun t : ℂ => (P₃ t,t)) ∧
    Disjoint (Set.range fun t : ℂ => (P₁,t)) (Set.range fun t : ℂ => (P₄,t)) ∧
    Disjoint (Set.range fun t : ℂ => (P₂,t)) (Set.range fun t : ℂ => (P₃ t,t)) ∧
    Disjoint (Set.range fun t : ℂ => (P₂,t)) (Set.range fun t : ℂ => (P₄,t)) ∧
    Disjoint (Set.range fun t : ℂ => (P₃ t,t)) (Set.range fun t : ℂ => (P₄,t)) := by
  exact ⟨disjoint_graphs_of_pointwise_ne _ _ (fun t => (four_projective_points_distinct t).1),
    disjoint_graphs_of_pointwise_ne _ _ (fun t => (four_projective_points_distinct t).2.1),
    disjoint_graphs_of_pointwise_ne _ _ (fun t => (four_projective_points_distinct t).2.2.1),
    disjoint_graphs_of_pointwise_ne _ _ (fun t => (four_projective_points_distinct t).2.2.2.1),
    disjoint_graphs_of_pointwise_ne _ _ (fun t => (four_projective_points_distinct t).2.2.2.2.1),
    disjoint_graphs_of_pointwise_ne _ _ (fun t => (four_projective_points_distinct t).2.2.2.2.2)⟩

open FailureOfSemipositiveMetricExtension.Cubics in
/-- The cubic common zero set, now interpreted in actual complex projective space. -/
theorem projective_cubic_common_zero_locus (v : Point) (hv : v ≠ 0) :
    (g₁ (v 0) (v 1) (v 2) = 0 ∧ g₂ (v 0) (v 1) (v 2) = 0 ∧
     g₃ (v 0) (v 1) (v 2) = 0 ∧ g₄ (v 0) (v 1) (v 2) = 0) ↔
    (Projectivization.mk ℂ v hv = P₁ ∨ Projectivization.mk ℂ v hv = P₂ ∨
     Projectivization.mk ℂ v hv = P₃ 0 ∨ Projectivization.mk ℂ v hv = P₄) := by
  constructor
  · intro h
    rcases (generators_common_zero_locus (v 0) (v 1) (v 2)).mp h with h₄ | h₁ | h₂ | h₃
    · apply Or.inr; apply Or.inr; apply Or.inr
      apply (Projectivization.mk_eq_mk_iff' ℂ v p₄ hv p₄_nonzero).mpr
      refine ⟨v 2, ?_⟩
      ext i; fin_cases i <;> simp [p₄, h₄.1, h₄.2]
    · apply Or.inl
      apply (Projectivization.mk_eq_mk_iff' ℂ v p₁ hv p₁_nonzero).mpr
      refine ⟨v 0, ?_⟩
      ext i; fin_cases i <;> simp [p₁, h₁.1, h₁.2]
    · apply Or.inr; apply Or.inl
      apply (Projectivization.mk_eq_mk_iff' ℂ v p₂ hv p₂_nonzero).mpr
      refine ⟨v 1, ?_⟩
      ext i; fin_cases i <;> simp [p₂, h₂.1, h₂.2]
    · apply Or.inr; apply Or.inr; apply Or.inl
      apply (Projectivization.mk_eq_mk_iff' ℂ v (p₃ 0) hv (p₃_nonzero 0)).mpr
      refine ⟨v 0, ?_⟩
      ext i; fin_cases i <;> simp [p₃, h₃.1, h₃.2]
  · rintro (h | h | h | h)
    · rcases (Projectivization.mk_eq_mk_iff' ℂ v p₁ hv p₁_nonzero).mp h with ⟨a,ha⟩
      rw [← ha]; simp [g₁,g₂,g₃,g₄,p₁,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
    · rcases (Projectivization.mk_eq_mk_iff' ℂ v p₂ hv p₂_nonzero).mp h with ⟨a,ha⟩
      rw [← ha]; simp [g₁,g₂,g₃,g₄,p₂,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
    · rcases (Projectivization.mk_eq_mk_iff' ℂ v (p₃ 0) hv (p₃_nonzero 0)).mp h with ⟨a,ha⟩
      rw [← ha]; simp [g₁,g₂,g₃,g₄,p₃,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
    · rcases (Projectivization.mk_eq_mk_iff' ℂ v p₄ hv p₄_nonzero).mp h with ⟨a,ha⟩
      rw [← ha]; simp [g₁,g₂,g₃,g₄,p₄,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
end FailureOfSemipositiveMetricExtension.Coordinates
