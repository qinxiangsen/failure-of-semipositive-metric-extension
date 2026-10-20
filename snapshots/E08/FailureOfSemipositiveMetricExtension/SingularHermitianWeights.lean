import FailureOfSemipositiveMetricExtension.GeneratedFiberMetrics
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Compatible extended-real weights on the actual line bundles. Positivity of
curvature is deliberately not a field: it must be proved separately. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold
open scoped Manifold ContDiff

structure SingularHermitianWeight (t : ℂ) (a : ℤ) (b : Fin 4 → ℤ) where
  weight : Index → Fiber t → WithBot ℝ
  compatible : ∀ i j p, p ∈ baseSet t i ∩ baseSet t j →
    weight j p = weight i p + (Real.log (Complex.normSq (gain t a b i j p)) : ℝ)

theorem gain_ne_zero (t : ℂ) (a : ℤ) (b : Fin 4 → ℤ) (i j : Index) (p : Fiber t)
    (hp : p ∈ baseSet t i ∩ baseSet t j) : gain t a b i j p ≠ 0 := by
  have h := gain_comp t a b i j i p ⟨hp,hp.1⟩
  rw [gain_self] at h
  intro hz
  rw [hz,mul_zero] at h
  exact zero_ne_one h

def logarithmicSectionWeight {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ}
    (s : SectionData t a b) (i : Index) (p : Fiber t) : WithBot ℝ :=
  if s.coefficient i p = 0 then ⊥ else (Real.log (Complex.normSq (s.coefficient i p)) : ℝ)

theorem logarithmicSectionWeight_transition {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ}
    (s : SectionData t a b) (i j : Index) (p : Fiber t) (hp : p ∈ baseSet t i ∩ baseSet t j) :
    logarithmicSectionWeight s j p = logarithmicSectionWeight s i p +
      (Real.log (Complex.normSq (gain t a b i j p)) : ℝ) := by
  have hg := gain_ne_zero t a b i j p hp
  have hc := s.compatible i j p hp
  unfold logarithmicSectionWeight
  by_cases hs : s.coefficient i p = 0
  · have hj : s.coefficient j p = 0 := by rw [← hc,hs,mul_zero]
    simp [hs,hj]
  · have hj : s.coefficient j p ≠ 0 := by rw [← hc]; exact mul_ne_zero hg hs
    simp only [hs,hj,if_false]
    rw [← hc,Complex.normSq_mul,Real.log_mul (ne_of_gt (Complex.normSq_pos.mpr hg))
      (ne_of_gt (Complex.normSq_pos.mpr hs))]
    simp [add_comm]

def divisorWeight {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ} (s : SectionData t a b) :
    SingularHermitianWeight t a b where
  weight := logarithmicSectionWeight s
  compatible := logarithmicSectionWeight_transition s

theorem divisorWeight_eq_bot_iff {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ}
    (s : SectionData t a b) (i : Index) (p : Fiber t) (hp : p ∈ baseSet t i) :
    (divisorWeight s).weight i p = ⊥ ↔ sectionValue s p = 0 := by
  rw [sectionValue_zero_iff s i p hp]
  change (if s.coefficient i p = 0 then ⊥ else
    (Real.log (Complex.normSq (s.coefficient i p)) : WithBot ℝ)) = ⊥ ↔ _
  split_ifs <;> simp_all

def smoothMetricWeight {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ}
    (h : SmoothHermitianMetric t a b) : SingularHermitianWeight t a b where
  weight i p := (-Real.log (h.coefficient i p) : ℝ)
  compatible i j p hp := by
    have hi := ne_of_gt (h.positive i p hp.1)
    have hj := ne_of_gt (h.positive j p hp.2)
    have hg := ne_of_gt (Complex.normSq_pos.mpr (gain_ne_zero t a b i j p hp))
    have he := congrArg Real.log (h.compatible i j p hp)
    rw [Real.log_mul hj hg] at he
    have he' : -Real.log (h.coefficient j p) =
      -Real.log (h.coefficient i p) + Real.log (Complex.normSq (gain t a b i j p)) := by linarith
    simpa using congrArg (fun x : ℝ => (x : WithBot ℝ)) he'

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
