import FailureOfSemipositiveMetricExtension.CentralTransverseLineBundleEquivalence

/-! The explicit restricted-bundle equivalence is complex analytic in both
 directions, giving an actual bundle isomorphism on the parametrized transverse line. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.CentralLine
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

theorem restrictionBundleEquiv_contMDiff (c : Data) (a : ℤ) (b : Fin 4 → ℤ) :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω (restrictionBundleEquiv c a b) := by
  intro z
  let e := selectedLineFrame a b z.proj
  let i := selectedAmbientFrame c a b z.proj
  have hz : z.proj ∈ restrictionPatch c e i := selected_patch c a b z.proj
  let el := (ProjectiveLineBundle.core (restrictionDegree a b)).localTriv e
  let er := restrictedTriv c a b i
  haveI : MemTrivializationAtlas el := ⟨⟨e,rfl⟩⟩
  apply (el.contMDiffAt_iff (show restrictionBundleEquiv c a b z ∈ el.source from hz.1)).mpr
  constructor
  · exact Bundle.contMDiffAt_proj (RestrictedFiber c a b)
  · have hF := ((restrictionFactor_contMDiffOn c a b e i ω).contMDiffAt
        ((restrictionPatch_isOpen c e i).mem_nhds hz)).comp z
        (Bundle.contMDiffAt_proj (RestrictedFiber c a b))
    have hR : ContMDiffAt (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω er z :=
      er.contMDiffOn.contMDiffAt (er.open_source.mem_nhds hz.2)
    apply (hF.smul hR.snd).congr_of_eventuallyEq
    have hU := ((restrictionPatch_isOpen c e i).preimage
      (FiberBundle.continuous_proj ℂ (RestrictedFiber c a b))).mem_nhds hz
    filter_upwards [hU] with w hw
    exact congrArg Prod.snd (restrictionBundleEquiv_localTriv c a b e i w hw)

theorem restrictionBundleEquiv_symm_contMDiff (c : Data) (a : ℤ) (b : Fin 4 → ℤ) :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω (restrictionBundleEquiv c a b).symm := by
  intro z
  let e := selectedLineFrame a b z.proj
  let i := selectedAmbientFrame c a b z.proj
  have hz : z.proj ∈ restrictionPatch c e i := selected_patch c a b z.proj
  let el := (ProjectiveLineBundle.core (restrictionDegree a b)).localTriv e
  let er := restrictedTriv c a b i
  haveI : MemTrivializationAtlas el := ⟨⟨e,rfl⟩⟩
  apply (er.contMDiffAt_iff (show (restrictionBundleEquiv c a b).symm z ∈ er.source from hz.2)).mpr
  constructor
  · exact Bundle.contMDiffAt_proj (ProjectiveLineBundle.core (restrictionDegree a b)).Fiber
  · have hF := ((restrictionFactor_inv_contMDiffOn c a b e i ω).contMDiffAt
        ((restrictionPatch_isOpen c e i).mem_nhds hz)).comp z
        (Bundle.contMDiffAt_proj (ProjectiveLineBundle.core (restrictionDegree a b)).Fiber)
    have hL : ContMDiffAt (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω el z :=
      el.contMDiffOn.contMDiffAt (el.open_source.mem_nhds hz.1)
    apply (hF.smul hL.snd).congr_of_eventuallyEq
    have hU := ((restrictionPatch_isOpen c e i).preimage
      (FiberBundle.continuous_proj ℂ (ProjectiveLineBundle.core (restrictionDegree a b)).Fiber)).mem_nhds hz
    filter_upwards [hU] with w hw
    exact congrArg Prod.snd (restrictionBundleEquiv_symm_localTriv c a b e i w hw)

/-- Actual analytic, base-preserving, fibrewise complex-linear isomorphism
param* core(a;b) ≃ O(a+b₀+b₁+b₂), with the standard pullback topology. -/
def restrictionBundleHomeomorph (c : Data) (a : ℤ) (b : Fin 4 → ℤ) :
    RestrictedTotal c a b ≃ₜ (ProjectiveLineBundle.core (restrictionDegree a b)).TotalSpace where
  toEquiv := restrictionBundleEquiv c a b
  continuous_toFun := (restrictionBundleEquiv_contMDiff c a b).continuous
  continuous_invFun := (restrictionBundleEquiv_symm_contMDiff c a b).continuous

theorem restrictionBundleHomeomorph_analytic (c : Data) (a : ℤ) (b : Fin 4 → ℤ) :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω (restrictionBundleHomeomorph c a b) ∧
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω (restrictionBundleHomeomorph c a b).symm :=
  ⟨restrictionBundleEquiv_contMDiff c a b,restrictionBundleEquiv_symm_contMDiff c a b⟩

/-- Canonical and pencil ambient indices give degree m-2 for every integer m. -/
theorem adjoint_restrictionDegree (m : ℤ) : restrictionDegree (1-2*m) (fun _ => m-1) = m-2 := by
  simp [restrictionDegree,Fin.sum_univ_four]
  ring

theorem pencil_restrictionDegree : restrictionDegree (-2) (fun _ => 1) = 1 := by
  norm_num [restrictionDegree,Fin.sum_univ_four]

theorem canonical_restrictionDegree : restrictionDegree 1 (fun _ => -1) = -2 := by
  norm_num [restrictionDegree,Fin.sum_univ_four]

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.CentralLine
