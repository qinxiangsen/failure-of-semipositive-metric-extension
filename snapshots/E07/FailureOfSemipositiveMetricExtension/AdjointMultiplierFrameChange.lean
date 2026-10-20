import FailureOfSemipositiveMetricExtension.CaoCentralFormAdapter
import FailureOfSemipositiveMetricExtension.FourthPowerWeights
import FailureOfSemipositiveMetricExtension.AdjointSectionIntegrability

/-! The actual distinguished adjoint two-form meets Cao's restricted multiplier
hypothesis in every independently chosen coordinate chart and line frame. The
canonical Jacobian is included as a genuine holomorphic stalk factor. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.CaoAdapter
noncomputable section
open Set TopologicalSpace CategoryTheory IsManifold
open scoped Manifold ContDiff
open FixedFiberBundle

/-- The canonical coordinate-change factor on the actual common patch. -/
def centralJacobianSection (a : ChartIndex) (d : PowerIndex) :
    C^∞⟮𝓘(ℂ,FixedFiber.Coord),CaoExtensionInterface.centralPatch family fourthPowerLine a d;𝓘(ℂ),ℂ⟯ :=
  functionSectionOn _ (FixedFiber.canonicalGain 0 (divisionChart d) a)
    ((FixedFiber.chartJacobian_contMDiffOn 0 a.1 d.1 a.2 d.2.1).mono
      (fun _ hp => ⟨hp.1,hp.2.1⟩))

/-- Exact equality of germs, not just equality of scalar formulas. -/
theorem sigmaCentralSection_germ_factorization (a : ChartIndex) (d : PowerIndex)
    (p : Fiber 0) (hp : p ∈ CaoExtensionInterface.centralPatch family fourthPowerLine a d) :
    (Multiplier.sheaf (Fiber 0)).presheaf.germ _ p hp
      (CaoExtensionInterface.centralCoefficientSection family fourthPowerLine sigmaCentralSection a d) =
      (holomorphicSheaf 0).presheaf.germ _ p hp (centralJacobianSection a d) *
        sigmaAdjointGerm d p hp.2 := by
  have hr : sigmaAdjointGerm d p hp.2 =
      (holomorphicSheaf 0).presheaf.germ _ p hp
        (functionSectionOn (CaoExtensionInterface.centralPatch family fourthPowerLine a d)
          (sigmaAdjointCoefficient d) ((sigmaAdjointCoefficient_analytic d).mono
            (fun _ hx => hx.2))) := by
    apply (holomorphicSheaf 0).presheaf.germ_ext _ hp
      (homOfLE (fun _ hx => hx.2)) (𝟙 _)
    apply Subtype.ext
    funext q
    rfl
  rw [hr,← map_mul]
  congr 1

theorem sigmaCentralSection_germ_mem_ellSquare (a : ChartIndex) (d : PowerIndex)
    (p : Fiber 0) (hp : p ∈ CaoExtensionInterface.centralPatch family fourthPowerLine a d) :
    (Multiplier.sheaf (Fiber 0)).presheaf.germ _ p hp
      (CaoExtensionInterface.centralCoefficientSection family fourthPowerLine sigmaCentralSection a d)
      ∈ ellPowerStalkIdeal 2 p := by
  rw [sigmaCentralSection_germ_factorization]
  exact (ellPowerStalkIdeal 2 p).mul_mem_left _ (sigmaAdjointGerm_mem_ellSquare d p hp.2)

/-- All actual coordinate/frame representatives satisfy the restricted
multiplier ideal required by the general literature theorem. -/
theorem sigmaCentralSection_inRestrictedMultiplier {U : Opens Total}
    (h : GlobalLineBundle.SingularWeightOn U (-2) (fun _ => 1))
    (hpsh : h.HasPlurisubharmonicWeights) (hc : h.centralDominatesH0) :
    CaoExtensionInterface.InRestrictedMultiplier family fourthPowerLine
      (fourthPowerWeight h hpsh) sigmaCentralSection := by
  intro a d p hp
  change Multiplier.IntegrableGerm (Fiber 0) 1
    (fun q => scaleWeight 4 (h.weight (GlobalLineBundle.divisionFrame d) (FixedFiber.inclusion 0 q))) p _
  rw [integrableGerm_scale_four_iff]
  obtain ⟨C,hC⟩ := hc
  apply Multiplier.IntegrableGerm.mono_of_local_comparison (Fiber 0) 4 _
    (centralH0.weight (divisionFrame d)) p _ C (frameOpen 0 (divisionFrame d)) hp.2.2
    (hC (divisionFrame d))
  rw [centralH0_multiplierGerm_iff 4 (divisionFrame d) p hp.2.2]
  exact sigmaCentralSection_germ_mem_ellSquare a d p hp

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.CaoAdapter
