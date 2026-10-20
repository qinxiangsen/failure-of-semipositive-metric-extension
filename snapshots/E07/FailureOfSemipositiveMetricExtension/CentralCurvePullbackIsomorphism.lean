import FailureOfSemipositiveMetricExtension.CentralCurvePullback

/-! Genuine analytic isomorphisms from the standard mathlib pullback along the
actual central projective line to O(a+b₃). Both directions preserve the base and
are complex linear on fibres. No degree/intersection comparison is assumed. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.CurvePullback
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

theorem bundleEquiv_contMDiff (a : ℤ) (b : Fin 4 → ℤ) :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω (bundleEquiv a b) := by
  intro z
  let i := (restrictedCore a b).indexAt z.proj
  have hp : z.proj ∈ ProjectiveLine.chartSet i := (restrictedCore a b).mem_baseSet_at z.proj
  let er := (restrictedCore a b).localTriv i
  let ep := pullbackTriv a b i
  haveI : MemTrivializationAtlas er := ⟨⟨i,rfl⟩⟩
  have hzp : z ∈ ep.source := by
    change z.proj ∈ (pullbackTriv a b i).baseSet
    rw [pullbackTriv_baseSet]
    exact hp
  apply (er.contMDiffAt_iff (show bundleEquiv a b z ∈ er.source from hp)).mpr
  constructor
  · exact Bundle.contMDiffAt_proj (PullbackFiber a b)
  · have hP : ContMDiffAt (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω ep z :=
      ep.contMDiffOn.contMDiffAt (ep.open_source.mem_nhds hzp)
    apply hP.snd.congr_of_eventuallyEq
    have hU := ((ProjectiveLine.chartSet_isOpen i).preimage
      (FiberBundle.continuous_proj ℂ (PullbackFiber a b))).mem_nhds hp
    filter_upwards [hU] with w hw
    exact congrArg Prod.snd (bundleEquiv_localTriv a b i w hw)

theorem bundleEquiv_symm_contMDiff (a : ℤ) (b : Fin 4 → ℤ) :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω (bundleEquiv a b).symm := by
  intro z
  let i := (restrictedCore a b).indexAt z.proj
  have hp : z.proj ∈ ProjectiveLine.chartSet i := (restrictedCore a b).mem_baseSet_at z.proj
  let er := (restrictedCore a b).localTriv i
  let ep := pullbackTriv a b i
  haveI : MemTrivializationAtlas er := ⟨⟨i,rfl⟩⟩
  have hzp : (bundleEquiv a b).symm z ∈ ep.source := by
    change z.proj ∈ (pullbackTriv a b i).baseSet
    rw [pullbackTriv_baseSet]
    exact hp
  apply (ep.contMDiffAt_iff hzp).mpr
  constructor
  · exact Bundle.contMDiffAt_proj (restrictedCore a b).Fiber
  · have hR : ContMDiffAt (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω er z :=
      er.contMDiffOn.contMDiffAt (er.open_source.mem_nhds hp)
    apply hR.snd.congr_of_eventuallyEq
    have hU := ((ProjectiveLine.chartSet_isOpen i).preimage
      (FiberBundle.continuous_proj ℂ (restrictedCore a b).Fiber)).mem_nhds hp
    filter_upwards [hU] with w hw
    exact congrArg Prod.snd (bundleEquiv_symm_localTriv a b i w hw)

def bundleHomeomorph (a : ℤ) (b : Fin 4 → ℤ) :
    PullbackTotal a b ≃ₜ (restrictedCore a b).TotalSpace where
  toEquiv := bundleEquiv a b
  continuous_toFun := (bundleEquiv_contMDiff a b).continuous
  continuous_invFun := (bundleEquiv_symm_contMDiff a b).continuous

/-- The actual restricted fibre is linearly isomorphic to the standard degree
bundle fibre, retaining the source's standard pullback interpretation. -/
def degreeFiberEquiv (a : ℤ) (b : Fin 4 → ℤ) (d : Direction) :
    PullbackFiber a b d ≃L[ℂ] (ProjectiveLineBundle.core (a+b 3)).Fiber d :=
  (fiberEquiv a b d).trans (restrictionFiberEquiv a b d)

/-- The standard analytic pullback of the surface bundle is genuinely
isomorphic, over the original P¹, to the actual O(a+b₃) line bundle. -/
def degreeHomeomorph (a : ℤ) (b : Fin 4 → ℤ) :
    PullbackTotal a b ≃ₜ (ProjectiveLineBundle.core (a+b 3)).TotalSpace :=
  (bundleHomeomorph a b).trans (restrictionBundleHomeomorph a b)

@[simp] theorem degreeHomeomorph_mk (a : ℤ) (b : Fin 4 → ℤ) (d : Direction)
    (v : PullbackFiber a b d) :
    degreeHomeomorph a b ⟨d,v⟩ = ⟨d,degreeFiberEquiv a b d v⟩ := rfl

@[simp] theorem degreeHomeomorph_projects (a : ℤ) (b : Fin 4 → ℤ) (z : PullbackTotal a b) :
    (degreeHomeomorph a b z).proj = z.proj := rfl

@[simp] theorem degreeHomeomorph_symm_projects (a : ℤ) (b : Fin 4 → ℤ)
    (z : (ProjectiveLineBundle.core (a+b 3)).TotalSpace) :
    ((degreeHomeomorph a b).symm z).proj = z.proj := rfl

theorem degreeHomeomorph_contMDiff (a : ℤ) (b : Fin 4 → ℤ) :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω (degreeHomeomorph a b) :=
  (restrictionBundleEquiv_contMDiff a b ω).comp (bundleEquiv_contMDiff a b)

theorem degreeHomeomorph_symm_contMDiff (a : ℤ) (b : Fin 4 → ℤ) :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω (degreeHomeomorph a b).symm :=
  (bundleEquiv_symm_contMDiff a b).comp (restrictionBundleEquiv_symm_contMDiff a b ω)

/-- The local coefficient identification is exact, in both actual bundles. -/
theorem degreeHomeomorph_localTriv (a : ℤ) (b : Fin 4 → ℤ) (i : Fin 2)
    (z : PullbackTotal a b) (hz : z.proj ∈ ProjectiveLine.chartSet i) :
    (ProjectiveLineBundle.core (a+b 3)).localTriv i (degreeHomeomorph a b z) =
      pullbackTriv a b i z :=
  (restrictionBundleEquiv_localTriv a b i (bundleEquiv a b z) hz).trans
    (bundleEquiv_localTriv a b i z hz)

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.CurvePullback
