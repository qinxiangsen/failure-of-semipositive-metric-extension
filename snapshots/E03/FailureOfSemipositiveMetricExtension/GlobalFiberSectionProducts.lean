import FailureOfSemipositiveMetricExtension.GlobalFiberSections
import FailureOfSemipositiveMetricExtension.GlobalSectionProducts

/-! Multiplication of genuine analytic sections on each actual fixed fibre.
The multidegree identity is pulled back from the verified global cocycle. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold
open scoped Manifold ContDiff

theorem gain_add (t : ℂ) (a c : ℤ) (b d : Fin 4 → ℤ) (i j : Index) (p : Fiber t)
    (hp : p ∈ baseSet t i ∩ baseSet t j) :
    gain t (a+c) (fun r => b r+d r) i j p = gain t a b i j p * gain t c d i j p :=
  FailureOfSemipositiveMetricExtension.GlobalLineBundle.gain_add a c b d i j (FixedFiber.inclusion t p) hp

/-- Pointwise product of genuine coherent analytic sections on the fixed fibre. -/
def multiplySections {t : ℂ} {a c : ℤ} {b d : Fin 4 → ℤ}
    (s : SectionData t a b) (v : SectionData t c d) :
    SectionData t (a+c) (fun r => b r+d r) where
  coefficient i p := s.coefficient i p * v.coefficient i p
  analytic i := (s.analytic i).smul (v.analytic i)
  compatible i j p hp := by
    rw [gain_add t a c b d i j p hp]
    calc
      (gain t a b i j p * gain t c d i j p) * (s.coefficient i p * v.coefficient i p) =
          (gain t a b i j p * s.coefficient i p) * (gain t c d i j p * v.coefficient i p) := by ring
      _ = _ := by rw [s.compatible i j p hp,v.compatible i j p hp]

@[simp] theorem multiplySections_coefficient {t : ℂ} {a c : ℤ} {b d : Fin 4 → ℤ}
    (s : SectionData t a b) (v : SectionData t c d) (i : Index) (p : Fiber t) :
    (multiplySections s v).coefficient i p = s.coefficient i p * v.coefficient i p := rfl

/-- The auxiliary fibre-coordinate choice is common to all multidegrees. -/
theorem core_indexAt_independent (t : ℂ) (a c : ℤ) (b d : Fin 4 → ℤ) (p : Fiber t) :
    (core t a b).indexAt p = (core t c d).indexAt p := rfl

theorem multiplySections_value {t : ℂ} {a c : ℤ} {b d : Fin 4 → ℤ}
    (s : SectionData t a b) (v : SectionData t c d) (p : Fiber t) :
    (show ℂ from sectionValue (multiplySections s v) p) =
      (show ℂ from sectionValue s p) * (show ℂ from sectionValue v p) := rfl

/-- Multiplication commutes exactly with restriction from the global manifold. -/
@[simp] theorem pullback_multiplySections (t : ℂ) {a c : ℤ} {b d : Fin 4 → ℤ}
    (s : FailureOfSemipositiveMetricExtension.GlobalLineBundle.SectionData a b)
    (v : FailureOfSemipositiveMetricExtension.GlobalLineBundle.SectionData c d) :
    pullback t (FailureOfSemipositiveMetricExtension.GlobalLineBundle.multiplySections s v) =
      multiplySections (pullback t s) (pullback t v) := rfl
end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
