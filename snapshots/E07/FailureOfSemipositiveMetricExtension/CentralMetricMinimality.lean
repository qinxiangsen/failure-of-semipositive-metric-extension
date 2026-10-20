import FailureOfSemipositiveMetricExtension.Literature.NegativeCurvePshRemoval
import FailureOfSemipositiveMetricExtension.NegativeCurveImmersionAdapter

/-! Minimal singularities of the ACTUAL prescribed metric, relative to the
precisely disclosed generic negative-curve literature corollary. Every concrete
geometric, section, tensor, degree and psh hypothesis is instantiated by proofs.
This does not identify a separately defined distributional-current Lelong number. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open NegativeCurveAdapter

/-- Actual residual existence for every actual compatible semipositive weight.
The external fact is universal; the actual interface fields are all proved. -/
theorem halfDivisorResidual_exists
    (h : SingularHermitianWeight 0 (-2) (fun _ => 1))
    (hh : HasPlurisubharmonicWeights h) : Nonempty (HalfDivisorResidual h) := by
  obtain ⟨r⟩ := Literature.negative_curve_psh_removal_via_zariski_siu_translation
    CaoAdapter.centralAtlas (line (-2) (fun _ => 1)) (line (-2) centralADegree)
      (line (-2) ellDegree) immersion 2 2 (by norm_num) (by norm_num)
      powerProduct generators divisor a_hasPullbackDegree ell_hasPullbackDegree
      (weight h) (weight_psh h hh)
  exact ⟨halfDivisorResidual h r⟩

/-- The prescribed h0 has minimal singularities in the standard all-psh-weights
comparison definition, on the actual compact central surface. -/
theorem centralH0_hasMinimalSingularities : HasMinimalSingularities centralH0 :=
  centralH0_minimal_of_residual_decompositions halfDivisorResidual_exists

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
