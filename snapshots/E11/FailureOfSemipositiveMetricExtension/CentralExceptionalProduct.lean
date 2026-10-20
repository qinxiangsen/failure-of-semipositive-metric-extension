import FailureOfSemipositiveMetricExtension.CentralCubicPullbacks
import FailureOfSemipositiveMetricExtension.GlobalFiberSectionProducts
import FailureOfSemipositiveMetricExtension.GlobalExceptionalProduct

/-! The genuine weighted exceptional denominator E₀ E₁ E₂ E₃² on the central
compact surface, with exactly the multidegree required for A. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle
open scoped Manifold ContDiff

def centralADegree (r : Fin 4) : ℤ := centralMultiplicity r

/-- Product of all four exceptional sections and one further copy of E₃. -/
def centralDenominator : SectionData 0 5 (fun r => -centralADegree r) where
  coefficient := (pullback 0 (FailureOfSemipositiveMetricExtension.GlobalLineBundle.multiplySections
    FailureOfSemipositiveMetricExtension.GlobalLineBundle.exceptionalProduct
    (FailureOfSemipositiveMetricExtension.GlobalLineBundle.exceptionalSection 3))).coefficient
  analytic := (pullback 0 (FailureOfSemipositiveMetricExtension.GlobalLineBundle.multiplySections
    FailureOfSemipositiveMetricExtension.GlobalLineBundle.exceptionalProduct
    (FailureOfSemipositiveMetricExtension.GlobalLineBundle.exceptionalSection 3))).analytic
  compatible i j p hp := by
    have h := (pullback 0 (FailureOfSemipositiveMetricExtension.GlobalLineBundle.multiplySections
      FailureOfSemipositiveMetricExtension.GlobalLineBundle.exceptionalProduct
      (FailureOfSemipositiveMetricExtension.GlobalLineBundle.exceptionalSection 3))).compatible i j p hp
    have hb : (fun r : Fin 4 => (-1 : ℤ) + FailureOfSemipositiveMetricExtension.GlobalLineBundle.exceptionalDegree 3 r) =
        (fun r => -centralADegree r) := by
      funext r
      fin_cases r <;> decide
    change gain 0 5 (fun r => -1 + FailureOfSemipositiveMetricExtension.GlobalLineBundle.exceptionalDegree 3 r) i j p * _ = _ at h
    conv at h => lhs; arg 1; rw [hb]
    exact h

theorem centralDenominator_coefficient (i : Index) (p : Fiber 0) :
    centralDenominator.coefficient i p =
      ∏ r, exceptionalCoefficient 0 r i p ^ centralMultiplicity r := by
  change (∏ r,FailureOfSemipositiveMetricExtension.GlobalLineBundle.exceptionalCoefficient r i (FixedFiber.inclusion 0 p)) *
      FailureOfSemipositiveMetricExtension.GlobalLineBundle.exceptionalCoefficient 3 i (FixedFiber.inclusion 0 p) = _
  simp [centralMultiplicity,Fin.prod_univ_succ,exceptionalCoefficient,pow_two,mul_assoc]

theorem centralDenominator_ne_zero (p : Fiber 0) (hp : p ∈ FixedFiber.awayCentres 0)
    (i : Index) (hi : p ∈ baseSet 0 i) : centralDenominator.coefficient i p ≠ 0 := by
  rw [centralDenominator_coefficient]
  apply Finset.prod_ne_zero_iff.mpr
  intro r _
  apply pow_ne_zero
  intro hz
  exact hp r ((exceptionalCoefficient_zero_iff 0 r i p hi).mp hz)

/-- Repackage the same actual cubic numerator with the exact sum of the two multidegrees. -/
def centralNumerator (k : Fin 4) :
    SectionData 0 ((-2 : ℤ)+5) (fun r => centralADegree r + -centralADegree r) where
  coefficient := (centralCubicSections k).coefficient
  analytic := (centralCubicSections k).analytic
  compatible i j p hp := by
    convert (centralCubicSections k).compatible i j p hp using 1 <;> norm_num

/-- Finite products of actual scalar analytic functions on a fixed fibre. -/
theorem scalarProduct_contMDiffOn {K : Type*} (t : ℂ) (S : Finset K) (U : Set (Fiber t))
    (f : K → Fiber t → ℂ)
    (hf : ∀ k ∈ S, ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω (f k) U) :
    ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω (fun p => ∏ k ∈ S,f k p) U := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (contMDiffOn_const (c := (1 : ℂ)))
  | @insert k S hk ih =>
    simp only [Finset.prod_insert hk]
    exact (hf k (Finset.mem_insert_self k S)).smul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

def cubicOtherDenominator (d : DivisionIndex) (p : Fiber 0) : ℂ :=
  ∏ j ∈ Finset.univ.erase d.1,
    exceptionalCoefficient 0 j (divisionFrame d) p ^ centralMultiplicity j

theorem cubicOtherDenominator_ne_zero (d : DivisionIndex) (p : Fiber 0)
    (hp : p ∈ divisionPatch 0 d) : cubicOtherDenominator d p ≠ 0 := by
  unfold cubicOtherDenominator
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply pow_ne_zero
  intro hz
  exact divisionPatch_avoids_other_centres 0 d p hp j (Finset.mem_erase.mp hj).1
    ((exceptionalCoefficient_zero_iff 0 j (divisionFrame d) p hp.2).mp hz)

theorem cubicOtherDenominator_contMDiffOn (d : DivisionIndex) :
    ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω (cubicOtherDenominator d) (divisionPatch 0 d) := by
  apply scalarProduct_contMDiffOn
  intro j _
  have h := (exceptionalCoefficient_contMDiffOn 0 j (divisionFrame d)).mono
    (show divisionPatch 0 d ⊆ baseSet 0 (divisionFrame d) from fun _ hp => hp.2)
  by_cases hj : j = 3
  · subst j
    simpa [centralMultiplicity,pow_two,smul_eq_mul] using h.smul h
  · simpa only [centralMultiplicity,hj,ite_false,pow_one] using h

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
