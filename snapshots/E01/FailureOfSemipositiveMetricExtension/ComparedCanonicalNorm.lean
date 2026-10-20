import FailureOfSemipositiveMetricExtension.CanonicalNormDensity
import FailureOfSemipositiveMetricExtension.GlobalSingularWeights

/-! Genuine finite global canonical norm for EVERY compatible candidate metric
satisfying the original one-sided bound. Infinity on the divisor is retained;
all density transformations and local finiteness hypotheses are proved here. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set MeasureTheory Topology
open scoped ENNReal
attribute [local instance] centralBorel centralBorelSpace

/-- Actual sigma coefficient times the actual extended inverse metric density. -/
def sigmaDensityForWeight (h : SingularHermitianWeight 0 (-2) (fun _ => 1))
    (d : DivisionIndex) (p : Fiber 0) : ℝ≥0∞ :=
  ENNReal.ofReal (Complex.normSq (sigmaAdjointCoefficient d p)) *
    Multiplier.exponentialWeight (h.weight (divisionFrame d) p) ^ 4

theorem sigmaDensityForWeight_transition (h : SingularHermitianWeight 0 (-2) (fun _ => 1))
    (d c : DivisionIndex) (p : Fiber 0) (hd : p ∈ divisionPatch 0 d) (hc : p ∈ divisionPatch 0 c) :
    sigmaDensityForWeight h c p =
      ENNReal.ofReal (Complex.normSq (FixedFiber.canonicalGain 0 (divisionChart d) (divisionChart c) p)) *
        sigmaDensityForWeight h d p := by
  unfold sigmaDensityForWeight
  rw [← sigmaAdjointCoefficient_compatible d c p hd hc,
    h.compatible (divisionFrame d) (divisionFrame c) p ⟨hd.2,hc.2⟩]
  exact Multiplier.weighted_norm_frame_change 4 _ _ _
    (gain_ne_zero 0 (-2) (fun _ => 1) (divisionFrame d) (divisionFrame c) p ⟨hd.2,hc.2⟩) _

theorem sigmaDensityForWeight_le (h : SingularHermitianWeight 0 (-2) (fun _ => 1)) (C : ℝ)
    (hcomp : ∀ i p, p ∈ baseSet 0 i → centralH0.weight i p + ((-C : ℝ) : WithBot ℝ) ≤ h.weight i p)
    (d : DivisionIndex) (p : Fiber 0) (hp : p ∈ divisionPatch 0 d) :
    sigmaDensityForWeight h d p ≤ ENNReal.ofReal (Real.exp C)^4 * sigmaAdjointExtendedDensity d p :=
  Multiplier.weightedDensity_le_of_comparison _ _ _ _ C (hcomp _ _ hp.2)

theorem sigmaDensityForWeight_patch_finite (h : SingularHermitianWeight 0 (-2) (fun _ => 1)) (C : ℝ)
    (hcomp : ∀ i p, p ∈ baseSet 0 i → centralH0.weight i p + ((-C : ℝ) : WithBot ℝ) ≤ h.weight i p)
    (P : CentralNormPatch) :
    (∫⁻ q in Metric.closedBall P.center P.radius,
      sigmaDensityForWeight h P.frame (FixedFiber.param 0 P.frame.1 P.frame.2.1 q)) < ⊤ := by
  have hle : (∫⁻ q in Metric.closedBall P.center P.radius,
      sigmaDensityForWeight h P.frame (FixedFiber.param 0 P.frame.1 P.frame.2.1 q)) ≤
      ∫⁻ q in Metric.closedBall P.center P.radius, ENNReal.ofReal (Real.exp C)^4 *
        sigmaAdjointExtendedDensity P.frame (FixedFiber.param 0 P.frame.1 P.frame.2.1 q) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with q hq
    exact sigmaDensityForWeight_le h C hcomp _ _ (P.closed_mapsTo hq)
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)] at hle
  exact hle.trans_lt (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) P.normIntegral_lt_top)

def comparedSigmaCanonicalDensity (h : SingularHermitianWeight 0 (-2) (fun _ => 1)) (C : ℝ)
    (hcomp : ∀ i p, p ∈ baseSet 0 i → centralH0.weight i p + ((-C : ℝ) : WithBot ℝ) ≤ h.weight i p) :
    CanonicalNormDensity where
  density := sigmaDensityForWeight h
  transition := sigmaDensityForWeight_transition h
  finite_on_patch := sigmaDensityForWeight_patch_finite h C hcomp

/-- The actual one-sided comparison implies finite total canonical norm for the
candidate restricted metric, not merely a collection of local estimates. -/
theorem sigma_compared_global_norm_finite (h : SingularHermitianWeight 0 (-2) (fun _ => 1)) (C : ℝ)
    (hcomp : ∀ i p, p ∈ baseSet 0 i → centralH0.weight i p + ((-C : ℝ) : WithBot ℝ) ≤ h.weight i p) :
    (comparedSigmaCanonicalDensity h C hcomp).globalMeasure univ < ⊤ :=
  CanonicalNormDensity.global_mass_finite _

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle

namespace FailureOfSemipositiveMetricExtension.GlobalLineBundle
noncomputable section
open Set MeasureTheory Topology TopologicalSpace
open scoped ENNReal
attribute [local instance] GlobalIncidence.FixedFiberBundle.centralBorel
  GlobalIncidence.FixedFiberBundle.centralBorelSpace

/-- The actual original arbitrary-neighbourhood metric hypothesis yields a
finite globally glued canonical norm on the whole central fibre. -/
theorem SingularWeightOn.sigma_finite_global_canonical_norm {U : Opens GlobalIncidence.Total}
    (h : SingularWeightOn U (-2) (fun _ => 1)) (hU : ContainsCentralFiber U)
    (hcomp : h.centralDominatesH0) :
    ∃ ρ : GlobalIncidence.FixedFiberBundle.CanonicalNormDensity,
      (∀ d p, ρ.density d p = GlobalIncidence.FixedFiberBundle.sigmaDensityForWeight
        (h.centralRestriction hU) d p) ∧ ρ.globalMeasure univ < ⊤ := by
  obtain ⟨C,hC⟩ := hcomp
  exact ⟨GlobalIncidence.FixedFiberBundle.comparedSigmaCanonicalDensity (h.centralRestriction hU) C hC,
    fun _ _ => rfl,GlobalIncidence.FixedFiberBundle.sigma_compared_global_norm_finite _ C hC⟩

end
end FailureOfSemipositiveMetricExtension.GlobalLineBundle
