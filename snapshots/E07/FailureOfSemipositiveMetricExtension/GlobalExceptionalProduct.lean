import FailureOfSemipositiveMetricExtension.GlobalSectionProducts
import FailureOfSemipositiveMetricExtension.GlobalExceptionalDensity

/-! The actual product of the four exceptional divisor sections. -/
namespace FailureOfSemipositiveMetricExtension.GlobalLineBundle
noncomputable section
open Set Bundle IsManifold FailureOfSemipositiveMetricExtension.GlobalIncidence
open scoped Manifold ContDiff

def exceptionalProduct : SectionData 4 (fun _ => -1) where
  coefficient i p := ∏ r, exceptionalCoefficient r i p
  analytic i := by
    simpa only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,smul_eq_mul] using
      (exceptionalCoefficient_contMDiffOn 0 i).smul
        ((exceptionalCoefficient_contMDiffOn 1 i).smul
          ((exceptionalCoefficient_contMDiffOn 2 i).smul (exceptionalCoefficient_contMDiffOn 3 i)))
  compatible i j p hp := by
    have h := (multiplySections
      (multiplySections (exceptionalSection 0) (exceptionalSection 1))
      (multiplySections (exceptionalSection 2) (exceptionalSection 3))).compatible i j p hp
    have hb : (fun r => (exceptionalDegree 0 r+exceptionalDegree 1 r)+
        (exceptionalDegree 2 r+exceptionalDegree 3 r)) = (fun _ : Fin 4 => (-1 : ℤ)) := by
      funext r
      fin_cases r <;> decide
    change gain 4 (fun r => (exceptionalDegree 0 r+exceptionalDegree 1 r)+
      (exceptionalDegree 2 r+exceptionalDegree 3 r)) i j p *
      ((exceptionalCoefficient 0 i p * exceptionalCoefficient 1 i p) *
        (exceptionalCoefficient 2 i p * exceptionalCoefficient 3 i p)) =
      ((exceptionalCoefficient 0 j p * exceptionalCoefficient 1 j p) *
        (exceptionalCoefficient 2 j p * exceptionalCoefficient 3 j p)) at h
    rw [hb] at h
    simpa only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,mul_assoc] using h

theorem exceptionalProduct_coefficient_ne_zero (p : Total) (hp : p ∈ awayCentres)
    (i : Index) (hi : p ∈ baseSet i) : exceptionalProduct.coefficient i p ≠ 0 := by
  change (∏ r,exceptionalCoefficient r i p) ≠ 0
  apply Finset.prod_ne_zero_iff.mpr
  intro r _
  exact fun hz => hp r ((exceptionalCoefficient_zero_iff r i p hi).mp hz)

theorem exceptionalProduct_value_zero_iff (p : Total) :
    sectionValue exceptionalProduct p = 0 ↔ ∃ r, blowdown p = centre r (projection p) := by
  let i := (core 4 (fun _ => -1)).indexAt p
  have hi : p ∈ baseSet i := (core 4 (fun _ => -1)).mem_baseSet_at p
  rw [sectionValue_zero_iff exceptionalProduct i p hi]
  change (∏ r,exceptionalCoefficient r i p) = 0 ↔ _
  simp only [Finset.prod_eq_zero_iff,Finset.mem_univ,true_and]
  exact exists_congr (fun r => exceptionalCoefficient_zero_iff r i p hi)
end
end FailureOfSemipositiveMetricExtension.GlobalLineBundle
