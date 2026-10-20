import FailureOfSemipositiveMetricExtension.CanonicalAdjunctionIsomorphism
import FailureOfSemipositiveMetricExtension.FixedFiberAdjointSections
import FailureOfSemipositiveMetricExtension.GlobalDivisionCover

/-! Genuine total-space adjoint bundles, with the actual canonical three-form
cocycle and the m-th power of the actual line-bundle cocycle. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalAdjoint
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

abbrev Index := GlobalLineBundle.DivisionIndex
abbrev patch := GlobalLineBundle.divisionPatch
abbrev frame := GlobalLineBundle.divisionFrame

def chart (d : Index) : GlobalCanonical.Index := (d.1,d.2.1)

def gain (m : ℕ) (d c : Index) (p : Total) : ℂ :=
  GlobalCanonical.canonicalGain (chart d) (chart c) p *
    GlobalLineBundle.gain (-2) (fun _ => 1) (frame d) (frame c) p ^ m

theorem gain_contMDiffOn (m : ℕ) (d c : Index) :
    ContMDiffOn 𝓘(ℂ,ChartCoord) 𝓘(ℂ) ω (gain m d c) (patch d ∩ patch c) := by
  have hk := (GlobalCanonical.chartJacobian_contMDiffOn c.1 d.1 c.2.1 d.2.1).mono
    (show patch d ∩ patch c ⊆ chartSource c.1 c.2.1 ∩ chartSource d.1 d.2.1 from
      fun _ h => ⟨h.2.1,h.1.1⟩)
  have hl := (GlobalLineBundle.gain_contMDiffOn (-2) (fun _ => 1) (frame d) (frame c) ω).mono
    (show patch d ∩ patch c ⊆ GlobalLineBundle.baseSet (frame d) ∩ GlobalLineBundle.baseSet (frame c) from
      fun _ h => ⟨h.1.2,h.2.2⟩)
  have hpow : ContMDiffOn 𝓘(ℂ,ChartCoord) 𝓘(ℂ) ω
      (fun p => GlobalLineBundle.gain (-2) (fun _ => 1) (frame d) (frame c) p ^ m) (patch d ∩ patch c) := by
    induction m with
    | zero => simpa using (contMDiffOn_const (c := (1 : ℂ)))
    | succ m ih => simpa only [pow_succ,smul_eq_mul] using ih.smul hl
  exact hk.smul hpow

def patchAt (p : Total) : Index := Classical.choose (GlobalLineBundle.divisionPatch_cover p)
theorem patchAt_mem (p : Total) : p ∈ patch (patchAt p) :=
  Classical.choose_spec (GlobalLineBundle.divisionPatch_cover p)

/-- The actual total-space K tensor L^m, in a common refinement of genuine frames. -/
def core (m : ℕ) : VectorBundleCore ℂ Total ℂ Index where
  baseSet := patch
  isOpen_baseSet := GlobalLineBundle.divisionPatch_isOpen
  indexAt := patchAt
  mem_baseSet_at := patchAt_mem
  coordChange d c p := gain m d c p • ContinuousLinearMap.id ℂ ℂ
  coordChange_self d p _ v := by simp [gain,GlobalLineBundle.gain_self]
  continuousOn_coordChange d c := (gain_contMDiffOn m d c).continuousOn.smul continuousOn_const
  coordChange_comp d c b p hp v := by
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul]
    change (_ * _^m) * ((_ * _^m) * v) = _
    rw [show ∀ K1 K2 L1 L2 : ℂ, (K1*L1^m)*((K2*L2^m)*v) = (K1*K2)*(L1*L2)^m*v from
      by intros; rw [mul_pow]; ring]
    rw [GlobalCanonical.canonicalGain_comp (chart d) (chart c) (chart b) p
      hp.1.1.1 hp.1.2.1 hp.2.1,
      GlobalLineBundle.gain_comp (-2) (fun _ => 1) (frame d) (frame c) (frame b) p
        ⟨⟨hp.1.1.2,hp.1.2.2⟩,hp.2.2⟩]
    rfl

instance core_isContMDiff (m : ℕ) : (core m).IsContMDiff 𝓘(ℂ,ChartCoord) ω where
  contMDiffOn_coordChange d c := (gain_contMDiffOn m d c).smul contMDiffOn_const

theorem core_finrank (m : ℕ) (p : Total) : Module.finrank ℂ ((core m).Fiber p) = 1 :=
  Module.finrank_self ℂ

theorem core_analytic (m : ℕ) : ContMDiffVectorBundle ω ℂ (core m).Fiber 𝓘(ℂ,ChartCoord) := inferInstance

/-- Restriction of the true canonical-times-L cocycle agrees with the fibre
adjoint cocycle, by the verified dt-Jacobian identity. -/
theorem gain_inclusion (t : ℂ) (m : ℕ) (d c : Index) (p : Fiber t)
    (hd : p ∈ FixedFiberBundle.divisionPatch t d) (hc : p ∈ FixedFiberBundle.divisionPatch t c) :
    gain m d c (FixedFiber.inclusion t p) = FixedFiberBundle.adjointGain t m d c p := by
  unfold gain FixedFiberBundle.adjointGain
  rw [GlobalCanonical.canonicalGain_inclusion t (chart d) (chart c) p hd.1 hc.1]
  rfl

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalAdjoint
