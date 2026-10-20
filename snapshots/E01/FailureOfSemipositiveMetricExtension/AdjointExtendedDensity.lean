import FailureOfSemipositiveMetricExtension.AdjointSectionIntegrability

/-! The actual extended ENNReal density of sigma, including the divisor, and
finite coordinate integrals under the original one-sided metric comparison. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set MeasureTheory TopologicalSpace IsManifold
open scoped Manifold ContDiff ENNReal

/-- The genuine nonnegative extended density; zero times infinity is zero. -/
def sigmaAdjointExtendedDensity (d : DivisionIndex) (p : Fiber 0) : ℝ≥0∞ :=
  ENNReal.ofReal (Complex.normSq (sigmaAdjointCoefficient d p)) *
    FailureOfSemipositiveMetricExtension.Multiplier.exponentialWeight (centralH0.weight (divisionFrame d) p) ^ 4

theorem sigmaAdjointWeightedDensity_nonneg (d : DivisionIndex) (p : Fiber 0) :
    0 ≤ sigmaAdjointWeightedDensity d p :=
  mul_nonneg (Complex.normSq_nonneg _) (Real.exp_pos _).le

/-- This equality also holds ON ell: both sides are exactly zero, since sigma
has the actual ell-square factor. No value at a singular point is discarded. -/
theorem sigmaAdjointExtendedDensity_eq_ofReal (d : DivisionIndex) (p : Fiber 0) :
    sigmaAdjointExtendedDensity d p = ENNReal.ofReal (sigmaAdjointWeightedDensity d p) := by
  by_cases he : ellSection.coefficient (divisionFrame d) p = 0
  · have hz : sigmaAdjointCoefficient d p = 0 := by
      simp [sigmaAdjointCoefficient,sigmaSection_coefficient,he]
    simp [sigmaAdjointExtendedDensity,sigmaAdjointWeightedDensity,hz]
  · have hw : centralH0.weight (divisionFrame d) p =
        (centralH0RealWeight (divisionFrame d) p : WithBot ℝ) := by
      simp [centralH0,he]
    rw [sigmaAdjointExtendedDensity,hw,FailureOfSemipositiveMetricExtension.Multiplier.exponentialWeight_coe,
      ← ENNReal.ofReal_pow (Real.exp_pos _).le,
      ← ENNReal.ofReal_mul (Complex.normSq_nonneg _)]
    congr 1
    unfold sigmaAdjointWeightedDensity
    congr 1
    rw [← Real.exp_nat_mul]
    congr 1
    ring

/-- Genuine finite nonnegative weighted integral on any compact coordinate set
contained in a valid actual adjoint frame. -/
theorem sigmaAdjointExtendedDensity_lintegral_lt_top (d : DivisionIndex)
    (K : Set FixedFiber.Coord) (hK : IsCompact K)
    (hd : K ⊆ FixedFiber.domain 0 d.1 d.2.1)
    (hp : MapsTo (FixedFiber.param 0 d.1 d.2.1) K (divisionPatch 0 d)) :
    (∫⁻ q in K, sigmaAdjointExtendedDensity d (FixedFiber.param 0 d.1 d.2.1 q) ∂volume) < ⊤ := by
  simp_rw [sigmaAdjointExtendedDensity_eq_ofReal]
  exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
    (fun q => sigmaAdjointWeightedDensity_nonneg d _))).mp
      (sigmaAdjointWeightedDensity_integrableOn d K hK hd hp).hasFiniteIntegral

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
