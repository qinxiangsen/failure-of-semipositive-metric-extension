import FailureOfSemipositiveMetricExtension.GlobalSingularWeights
import FailureOfSemipositiveMetricExtension.CentralMultiplierSheaf
import FailureOfSemipositiveMetricExtension.MultiplierComparison

/-! Actual extension-weight comparison preserves the actual sigma germ's
integrability on the central fibre. This is a proved analytic step of the
obstruction argument, not an assumed extension or nonextension theorem. -/
namespace FailureOfSemipositiveMetricExtension.GlobalLineBundle
noncomputable section
open Set TopologicalSpace

theorem SingularWeightOn.sigma_germ_integrable_of_dominates
    {U : Opens GlobalIncidence.Total} (h : SingularWeightOn U (-2) (fun _ => 1))
    (hcmp : h.centralDominatesH0) (i : Index) (p : GlobalIncidence.Fiber 0)
    (hp : p ∈ GlobalIncidence.FixedFiberBundle.baseSet 0 i) :
    FailureOfSemipositiveMetricExtension.Multiplier.IntegrableGerm (GlobalIncidence.Fiber 0) 4
      (fun q => h.weight i (GlobalIncidence.FixedFiber.inclusion 0 q)) p
      (GlobalIncidence.FixedFiberBundle.sectionGerm
        GlobalIncidence.FixedFiberBundle.sigmaSection i p hp) := by
  obtain ⟨C,hC⟩ := hcmp
  exact FailureOfSemipositiveMetricExtension.Multiplier.IntegrableGerm.mono_of_local_comparison
    (GlobalIncidence.Fiber 0) 4 _ _ p _ C
    (GlobalIncidence.FixedFiberBundle.frameOpen 0 i) hp (hC i)
    (GlobalIncidence.FixedFiberBundle.sigmaSection_germ_weighted_integrable i p hp)

end
end FailureOfSemipositiveMetricExtension.GlobalLineBundle
