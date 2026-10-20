import FailureOfSemipositiveMetricExtension.Literature.CaoProjectivePsh
import FailureOfSemipositiveMetricExtension.CaoImmersionAdapter
import FailureOfSemipositiveMetricExtension.CaoDtRestrictionAdapter
import FailureOfSemipositiveMetricExtension.AdjointMultiplierFrameChange
import FailureOfSemipositiveMetricExtension.MetricPlurisubharmonicity

/-! Actual semipositive metric nonextension on every neighbourhood of the whole
central fibre. All adapters to the universal literature extension theorem are
proved for the constructed complex manifold, true line bundle, actual psh
weights, holomorphic germs, and tangent alternating forms. This does not assert
the separately unfinished minimal-singularity or algebraic blowup claims. -/
namespace FailureOfSemipositiveMetricExtension.GlobalLineBundle
noncomputable section
open Set TopologicalSpace
open GlobalIncidence GlobalIncidence.CaoAdapter

/-- The precise one-sided metric nonextension assertion. The original comparison
also proves componentwise well-defined restriction, so no extra restriction
hypothesis is needed in this implication. -/
theorem no_semipositive_metric_dominating_centralH0 (U : Opens Total)
    (hU : ContainsCentralFiber U) :
    ¬ ∃ h : SingularWeightOn U (-2) (fun _ => 1),
      h.HasPlurisubharmonicWeights ∧ h.centralDominatesH0 := by
  rintro ⟨h,hpsh,hc⟩
  obtain ⟨r,hr,_,S,hS⟩ :=
    Literature.cao_extension_via_projective_immersion_psh_translation family fourthPowerLine
      immersion U hU (fourthPowerWeight h hpsh) (fourthPowerWeight_wellDefined h hpsh hc)
      sigmaCentralSection (sigmaCentralSection_inRestrictedMultiplier h hpsh hc)
  apply sigmaCentralSection_no_extension (CaoExtensionInterface.discDomain family r) ?_ ⟨S,hS⟩
  intro p
  change GlobalIncidence.projection (FixedFiber.inclusion 0 p) ∈ Metric.ball (0 : ℂ) r
  simpa using hr

/-- No exact semipositive extension of the actual prescribed metric exists. -/
theorem no_exact_semipositive_extension (U : Opens Total) (hU : ContainsCentralFiber U) :
    ¬ ∃ h : SingularWeightOn U (-2) (fun _ => 1),
      h.HasPlurisubharmonicWeights ∧ h.centralExactH0 := by
  rintro ⟨h,hpsh,he⟩
  exact no_semipositive_metric_dominating_centralH0 U hU
    ⟨h,hpsh,h.centralExactH0_dominates he⟩

/-- Two actual weights have uniformly bounded difference, in extended-value
inequality form, including their common pole set. -/
def SingularWeightOn.centralSameBoundedSingularityType {U : Opens Total}
    (h : SingularWeightOn U (-2) (fun _ => 1)) : Prop :=
  ∃ C : ℝ, ∀ (i : Index) (p : Fiber 0), p ∈ FixedFiberBundle.baseSet 0 i →
    FixedFiberBundle.centralH0.weight i p + ((-C : ℝ) : WithBot ℝ) ≤
      h.weight i (FixedFiber.inclusion 0 p) ∧
    h.weight i (FixedFiber.inclusion 0 p) + ((-C : ℝ) : WithBot ℝ) ≤
      FixedFiberBundle.centralH0.weight i p

theorem no_semipositive_extension_same_bounded_singularity_type (U : Opens Total)
    (hU : ContainsCentralFiber U) :
    ¬ ∃ h : SingularWeightOn U (-2) (fun _ => 1),
      h.HasPlurisubharmonicWeights ∧ h.centralSameBoundedSingularityType := by
  rintro ⟨h,hpsh,C,hC⟩
  exact no_semipositive_metric_dominating_centralH0 U hU
    ⟨h,hpsh,C,fun i p hp => (hC i p hp).1⟩

/-- The constructed central metric is semipositive and satisfies the actual
neighbourhood nonextension obstruction. This packages no minimality assertion. -/
theorem prescribed_semipositive_metric_nonextension :
    FixedFiberBundle.HasPlurisubharmonicWeights FixedFiberBundle.centralH0 ∧
      ∀ U : Opens Total, ContainsCentralFiber U →
        ¬ ∃ h : SingularWeightOn U (-2) (fun _ => 1),
          h.HasPlurisubharmonicWeights ∧ h.centralDominatesH0 :=
  ⟨FixedFiberBundle.centralH0_plurisubharmonic,no_semipositive_metric_dominating_centralH0⟩

end
end FailureOfSemipositiveMetricExtension.GlobalLineBundle
