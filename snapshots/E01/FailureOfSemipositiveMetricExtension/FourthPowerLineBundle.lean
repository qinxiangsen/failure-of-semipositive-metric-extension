import FailureOfSemipositiveMetricExtension.CaoFamilyAdapter
import FailureOfSemipositiveMetricExtension.GlobalAdjointBundle

/-! The genuine fourth tensor-power line bundle on the common geometric/frame
refinement. Its cocycle is literally the fourth power of the actual L cocycle. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.CaoAdapter
noncomputable section
open Set Bundle IsManifold
open scoped Manifold ContDiff

abbrev PowerIndex := GlobalLineBundle.DivisionIndex

def powerGain (d c : PowerIndex) (p : Total) : ℂ :=
  GlobalLineBundle.gain (-2) (fun _ => 1)
    (GlobalLineBundle.divisionFrame d) (GlobalLineBundle.divisionFrame c) p ^ 4

theorem powerGain_contMDiffOn (d c : PowerIndex) :
    ContMDiffOn 𝓘(ℂ,ChartCoord) 𝓘(ℂ) ω (powerGain d c)
      (GlobalLineBundle.divisionPatch d ∩ GlobalLineBundle.divisionPatch c) := by
  have h := (GlobalLineBundle.gain_contMDiffOn (-2) (fun _ => 1)
    (GlobalLineBundle.divisionFrame d) (GlobalLineBundle.divisionFrame c) ω).mono
    (show GlobalLineBundle.divisionPatch d ∩ GlobalLineBundle.divisionPatch c ⊆
      GlobalLineBundle.baseSet (GlobalLineBundle.divisionFrame d) ∩
        GlobalLineBundle.baseSet (GlobalLineBundle.divisionFrame c) from fun p hp => ⟨hp.1.2,hp.2.2⟩)
  have hp : powerGain d c = fun p =>
      GlobalLineBundle.gain (-2) (fun _ => 1) (GlobalLineBundle.divisionFrame d) (GlobalLineBundle.divisionFrame c) p *
      (GlobalLineBundle.gain (-2) (fun _ => 1) (GlobalLineBundle.divisionFrame d) (GlobalLineBundle.divisionFrame c) p *
      (GlobalLineBundle.gain (-2) (fun _ => 1) (GlobalLineBundle.divisionFrame d) (GlobalLineBundle.divisionFrame c) p *
      GlobalLineBundle.gain (-2) (fun _ => 1) (GlobalLineBundle.divisionFrame d) (GlobalLineBundle.divisionFrame c) p)) := by
    funext p; unfold powerGain; ring
  rw [hp]
  simpa only [smul_eq_mul] using h.smul (h.smul (h.smul h))

def powerCore : VectorBundleCore ℂ Total ℂ PowerIndex where
  baseSet := GlobalLineBundle.divisionPatch
  isOpen_baseSet := GlobalLineBundle.divisionPatch_isOpen
  indexAt := GlobalAdjoint.patchAt
  mem_baseSet_at := GlobalAdjoint.patchAt_mem
  coordChange d c p := powerGain d c p • ContinuousLinearMap.id ℂ ℂ
  coordChange_self d p _ v := by simp [powerGain,GlobalLineBundle.gain_self]
  continuousOn_coordChange d c := (powerGain_contMDiffOn d c).continuousOn.smul continuousOn_const
  coordChange_comp d c b p hp v := by
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul,powerGain]
    rw [← mul_assoc,← mul_pow,GlobalLineBundle.gain_comp (-2) (fun _ => 1)
      (GlobalLineBundle.divisionFrame d) (GlobalLineBundle.divisionFrame c) (GlobalLineBundle.divisionFrame b) p
      ⟨⟨hp.1.1.2,hp.1.2.2⟩,hp.2.2⟩]

instance powerCore_isContMDiff : powerCore.IsContMDiff 𝓘(ℂ,ChartCoord) ω where
  contMDiffOn_coordChange d c := (powerGain_contMDiffOn d c).smul contMDiffOn_const

/-- The actual analytic line bundle supplied to the generic Cao interface. -/
def fourthPowerLine : CaoExtensionInterface.AnalyticLineBundle (M := Total) PowerIndex where
  core := powerCore
  analytic := inferInstance
  gain := powerGain
  coordChange_eq _ _ _ _ := rfl

@[simp] theorem fourthPowerLine_gain (d c : PowerIndex) (p : Total) :
    fourthPowerLine.gain d c p = powerGain d c p := rfl

@[simp] theorem fourthPowerLine_baseSet (d : PowerIndex) :
    fourthPowerLine.core.baseSet d = GlobalLineBundle.divisionPatch d := rfl

theorem powerGain_inclusion (d c : PowerIndex) (p : Fiber 0) :
    powerGain d c (FixedFiber.inclusion 0 p) =
      FixedFiberBundle.gain 0 (-2) (fun _ => 1)
        (FixedFiberBundle.divisionFrame d) (FixedFiberBundle.divisionFrame c) p ^ 4 := rfl

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.CaoAdapter
