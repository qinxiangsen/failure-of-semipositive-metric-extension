import FailureOfSemipositiveMetricExtension.GlobalHyperplanePullback
import FailureOfSemipositiveMetricExtension.FixedFiberCanonicalAdjoint
import FailureOfSemipositiveMetricExtension.CentralAdjointSection
import FailureOfSemipositiveMetricExtension.CentralCubicDivision
import FailureOfSemipositiveMetricExtension.CentralSingularWeight

/-! Exact same-object divisor nomenclature in transition functions. `paperGain`
uses the actual H pullback bundle and actual simply vanishing exceptional
section bundles, not an uninterpreted divisor lattice. Standard line-bundle
tensor/dual and effective-divisor correspondences interpret these identities.
The identities do not assert a scheme blow-up isomorphism. -/
namespace FailureOfSemipositiveMetricExtension.GlobalLineBundle.PaperDivisors
noncomputable section
open Set GlobalIncidence
open scoped BigOperators

/-- Transition function of d H + sum n_r E_r, before invoking the standard
tensor/divisor correspondence. Every factor is an already constructed bundle. -/
def paperGain (d : ℤ) (n : Fin 4 → ℤ) (i j : Index) (p : Total) : ℂ :=
  gain 1 (fun _ => 0) i j p ^ d * ∏ r, gain 1 (exceptionalDegree r) i j p ^ n r

private theorem prod_power_sum (z : ℂ) (hz : z ≠ 0) (n : Fin 4 → ℤ)
    (s : Finset (Fin 4)) : (∏ r ∈ s, z ^ n r) = z ^ (∑ r ∈ s, n r) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert r s hr ih =>
    simp only [Finset.prod_insert hr,Finset.sum_insert hr,ih,zpow_add₀ hz]

/-- Converts all paper H/E coefficients to the original ambient-factor core
using actual transition functions on every overlap of the actual total space. -/
theorem paperGain_eq_actual_gain (d : ℤ) (n : Fin 4 → ℤ) (i j : Index) (p : Total)
    (hp : p ∈ baseSet i ∩ baseSet j) :
    paperGain d n i j p = gain (d + ∑ r, n r) (fun r => -n r) i j p := by
  have hz := ProjectivePlaneBundle.ratio_ne_zero i.1 j.1 (blowdown p) hp.1.1 hp.2.1
  simp only [paperGain,Hyperplane.gain_hyperplane,gain_exceptional,
    ProjectivePlaneBundle.gain,zpow_one,mul_zpow,inv_zpow,← zpow_neg]
  rw [Finset.prod_mul_distrib,prod_power_sum _ hz]
  unfold gain ProjectivePlaneBundle.gain ProjectiveLineBundle.gain
  rw [zpow_add₀ hz]
  ring

theorem L_named_gain (i j : Index) (p : Total) (hp : p ∈ baseSet i ∩ baseSet j) :
    paperGain 2 (fun _ => -1) i j p = gain (-2) (fun _ => 1) i j p := by
  simpa using paperGain_eq_actual_gain 2 (fun _ => -1) i j p hp

theorem K_named_gain (i j : Index) (p : Total) (hp : p ∈ baseSet i ∩ baseSet j) :
    paperGain (-3) (fun _ => 1) i j p = gain 1 (fun _ => -1) i j p := by
  simpa using paperGain_eq_actual_gain (-3) (fun _ => 1) i j p hp

theorem ell_named_gain (i j : Index) (p : Total) (hp : p ∈ baseSet i ∩ baseSet j) :
    paperGain 1 ![-1,-1,-1,0] i j p =
      gain (-2) FixedFiberBundle.ellDegree i j p := by
  convert paperGain_eq_actual_gain 1 ![-1,-1,-1,0] i j p hp using 1

theorem A_named_gain (i j : Index) (p : Total) (hp : p ∈ baseSet i ∩ baseSet j) :
    paperGain 3 ![-1,-1,-1,-2] i j p =
      gain (-2) FixedFiberBundle.centralADegree i j p := by
  convert paperGain_eq_actual_gain 3 ![-1,-1,-1,-2] i j p hp using 1

theorem Q_named_gain (i j : Index) (p : Total) (hp : p ∈ baseSet i ∩ baseSet j) :
    paperGain 3 ![-1,-1,-1,-3] i j p =
      gain (-3) FixedFiberBundle.qDegree i j p := by
  convert paperGain_eq_actual_gain 3 ![-1,-1,-1,-3] i j p hp using 1

/-- These are the actual restricted cocycles, not a separate fibre construction. -/
theorem named_gain_restricts (d : ℤ) (n : Fin 4 → ℤ) (t : ℂ)
    (i j : Index) (p : Fiber t) (hp : p ∈ FixedFiberBundle.baseSet t i ∩
      FixedFiberBundle.baseSet t j) :
    paperGain d n i j (FixedFiber.inclusion t p) =
      FixedFiberBundle.gain t (d + ∑ r, n r) (fun r => -n r) i j p :=
  paperGain_eq_actual_gain d n i j (FixedFiber.inclusion t p) hp

/-- The named -3H+sum E gain is tied to the actual derivative-defined
canonical cocycle by the previously proved nonvanishing frame factors. -/
theorem K_named_canonical_transition (t : ℂ)
    (d c : FixedFiberBundle.DivisionIndex) (p : Fiber t)
    (hd : p ∈ FixedFiberBundle.divisionPatch t d)
    (hc : p ∈ FixedFiberBundle.divisionPatch t c) :
    FixedFiber.canonicalGain t (FixedFiberBundle.divisionChart d)
      (FixedFiberBundle.divisionChart c) p * FixedFiberBundle.canonicalFactor t d p =
      paperGain (-3) (fun _ => 1) (FixedFiberBundle.divisionFrame d)
        (FixedFiberBundle.divisionFrame c) (FixedFiber.inclusion t p) *
          FixedFiberBundle.canonicalFactor t c p := by
  rw [K_named_gain _ _ _ ⟨hd.2,hc.2⟩]
  exact FixedFiberBundle.canonicalFactor_transition t d c p hd hc

/-- The paper's A+ell=2L and K+4L identifications refer to the actual
central gains, and sigma is exactly the product of the actual sections. -/
theorem central_named_tensor_and_section_certificate (i j : Index) (p : Fiber 0)
    (hp : p ∈ FixedFiberBundle.baseSet 0 i ∩ FixedFiberBundle.baseSet 0 j) :
    (paperGain 3 ![-1,-1,-1,-2] i j (FixedFiber.inclusion 0 p) *
      paperGain 1 ![-1,-1,-1,0] i j (FixedFiber.inclusion 0 p) =
        paperGain 2 (fun _ => -1) i j (FixedFiber.inclusion 0 p) ^ 2) ∧
    (FixedFiberBundle.gain 0 (-7) (fun _ => 3) i j p =
      paperGain (-3) (fun _ => 1) i j (FixedFiber.inclusion 0 p) *
        paperGain 2 (fun _ => -1) i j (FixedFiber.inclusion 0 p) ^ 4) ∧
    FixedFiberBundle.sigmaSection.coefficient i p =
      FixedFiberBundle.ellSection.coefficient i p ^ 2 *
        FixedFiberBundle.qSection.coefficient i p := by
  rw [A_named_gain i j _ hp,ell_named_gain i j _ hp,L_named_gain i j _ hp,
    K_named_gain i j _ hp]
  exact ⟨FixedFiberBundle.central_gain_square i j p hp,
    FixedFiberBundle.sigmaGain_canonical_four_L 0 i j p hp,
    FixedFiberBundle.sigmaSection_coefficient i p⟩

/-- All four exceptional factors have exactly the specified centre-fibre zero
set and a genuine radial equation of multiplicity one at every zero. -/
theorem actual_exceptional_divisor_naming (r : Fin 4) :
    (∀ p : Total, sectionValue (exceptionalSection r) p = 0 ↔
      blowdown p = centre r (projection p)) ∧
    ∀ p : Total, sectionValue (exceptionalSection r) p = 0 →
      ∃ (e : Fin 2) (q : ChartCoord) (i : Index),
        p = chartParam r e q ∧ q ∈ chartDomain r e ∧ q.1.1 = 0 ∧ p ∈ baseSet i ∧
        ∀ q' : ChartCoord, exceptionalCoefficient r i (chartParam r e q') = q'.1.1 :=
  ⟨exceptionalSection_zero_iff r,exceptionalSection_local_simple_zero r⟩

end
end FailureOfSemipositiveMetricExtension.GlobalLineBundle.PaperDivisors
