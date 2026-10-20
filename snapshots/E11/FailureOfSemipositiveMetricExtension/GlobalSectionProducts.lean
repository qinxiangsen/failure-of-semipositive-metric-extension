import FailureOfSemipositiveMetricExtension.GlobalBundleSections

/-! Multiplication of genuine analytic sections with the verified multidegree cocycles. -/
namespace FailureOfSemipositiveMetricExtension.GlobalLineBundle
noncomputable section
open Set Bundle IsManifold FailureOfSemipositiveMetricExtension.GlobalIncidence
open scoped Manifold ContDiff

theorem gain_add (a c : ℤ) (b d : Fin 4 → ℤ) (i j : Index) (p : Total)
    (hp : p ∈ baseSet i ∩ baseSet j) :
    gain (a+c) (fun r => b r+d r) i j p = gain a b i j p * gain c d i j p := by
  unfold gain FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle.gain FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.gain
  rw [zpow_add₀ (FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle.ratio_ne_zero i.1 j.1 (blowdown p) hp.1.1 hp.2.1)]
  have he : (∏ r, FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.ratio (i.2 r) (j.2 r) (directions p r) ^ (b r+d r)) =
      ∏ r, FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.ratio (i.2 r) (j.2 r) (directions p r) ^ b r *
        FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.ratio (i.2 r) (j.2 r) (directions p r) ^ d r := by
    apply Finset.prod_congr rfl
    intro r _
    exact zpow_add₀ (FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.ratio_ne_zero
      (i.2 r) (j.2 r) (directions p r) (hp.1.2 r) (hp.2.2 r)) _ _
  rw [he,Finset.prod_mul_distrib]
  ring

def multiplySections {a c : ℤ} {b d : Fin 4 → ℤ} (s : SectionData a b) (t : SectionData c d) :
    SectionData (a+c) (fun r => b r+d r) where
  coefficient i p := s.coefficient i p * t.coefficient i p
  analytic i := (s.analytic i).smul (t.analytic i)
  compatible i j p hp := by
    rw [gain_add a c b d i j p hp]
    calc
      (gain a b i j p * gain c d i j p) * (s.coefficient i p * t.coefficient i p) =
          (gain a b i j p * s.coefficient i p) * (gain c d i j p * t.coefficient i p) := by ring
      _ = _ := by rw [s.compatible i j p hp,t.compatible i j p hp]

/-- The auxiliary fibre-coordinate choice is common to all multidegrees. -/
theorem core_indexAt_independent (a c : ℤ) (b d : Fin 4 → ℤ) (p : Total) :
    (core a b).indexAt p = (core c d).indexAt p := rfl

theorem multiplySections_value {a c : ℤ} {b d : Fin 4 → ℤ}
    (s : SectionData a b) (t : SectionData c d) (p : Total) :
    (show ℂ from sectionValue (multiplySections s t) p) =
      (show ℂ from sectionValue s p) * (show ℂ from sectionValue t p) := rfl
end
end FailureOfSemipositiveMetricExtension.GlobalLineBundle
