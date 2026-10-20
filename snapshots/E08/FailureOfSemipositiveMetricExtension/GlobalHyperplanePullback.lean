import FailureOfSemipositiveMetricExtension.GlobalAnalyticLineBundle
import FailureOfSemipositiveMetricExtension.GlobalSectionProducts
import FailureOfSemipositiveMetricExtension.GlobalExceptionalOrder
import Mathlib.Geometry.Manifold.VectorBundle.Pullback

/-! Concrete divisor naming: the degree-(1;0,0,0,0) bundle is the actual
mathlib pullback of the homogeneous degree-one bundle on P². This retains the
pullback topology, proves holomorphicity in both directions and identifies
complex-linear fibres. No Picard or Cartier identification is assumed. -/
namespace FailureOfSemipositiveMetricExtension.GlobalLineBundle.Hyperplane
noncomputable section
open Set Bundle IsManifold Topology GlobalIncidence
open scoped Manifold ContDiff BigOperators

def analyticBlowdown :
    C^ω⟮𝓘(ℂ,ChartCoord), Total; 𝓘(ℂ,ℂ × ℂ), ProjectivePlane.Point⟯ :=
  ⟨blowdown,blowdown_contMDiff ω⟩

abbrev HCore := core 1 (fun _ => 0)
abbrev PullbackFiber := analyticBlowdown *ᵖ (ProjectivePlaneBundle.core 1).Fiber
abbrev PullbackTotal := TotalSpace ℂ PullbackFiber

def pullbackTriv (a : Fin 3) : Trivialization ℂ (π ℂ PullbackFiber) :=
  ((ProjectivePlaneBundle.core 1).localTriv a).pullback analyticBlowdown

instance pullbackTriv_mem_atlas (a : Fin 3) : MemTrivializationAtlas (pullbackTriv a) := by
  haveI : MemTrivializationAtlas ((ProjectivePlaneBundle.core 1).localTriv a) := ⟨⟨a,rfl⟩⟩
  exact ⟨⟨(ProjectivePlaneBundle.core 1).localTriv a,inferInstance,rfl⟩⟩

@[simp] theorem gain_hyperplane (i j : Index) (p : Total) :
    gain 1 (fun _ => 0) i j p = ProjectivePlaneBundle.gain 1 i.1 j.1 (blowdown p) := by
  simp [gain,ProjectiveLineBundle.gain]

def fibreEquiv (p : Total) : HCore.Fiber p ≃L[ℂ] PullbackFiber p :=
  ContinuousLinearEquiv.refl ℂ ℂ

def bundleEquiv : HCore.TotalSpace ≃ PullbackTotal where
  toFun z := ⟨z.proj,fibreEquiv z.proj z.2⟩
  invFun z := ⟨z.proj,(fibreEquiv z.proj).symm z.2⟩
  left_inv z := by cases z; rfl
  right_inv z := by cases z; rfl

@[simp] theorem bundleEquiv_projects (z : HCore.TotalSpace) :
    (bundleEquiv z).proj = z.proj := rfl

@[simp] theorem bundleEquiv_symm_projects (z : PullbackTotal) :
    (bundleEquiv.symm z).proj = z.proj := rfl

theorem bundleEquiv_localTriv (i : Index) (z : HCore.TotalSpace) :
    pullbackTriv i.1 (bundleEquiv z) = HCore.localTriv i z := by
  change (z.proj,((ProjectivePlaneBundle.core 1).localTriv i.1
    ⟨blowdown z.proj,(show ℂ from z.2)⟩).2) = _
  rw [VectorBundleCore.localTriv_apply,VectorBundleCore.localTriv_apply]
  congr 1
  simp only [core,ProjectivePlaneBundle.core,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply,smul_eq_mul,gain_hyperplane]

theorem bundleEquiv_symm_localTriv (i : Index) (z : PullbackTotal) :
    HCore.localTriv i (bundleEquiv.symm z) = pullbackTriv i.1 z :=
  (bundleEquiv_localTriv i (bundleEquiv.symm z)).symm

theorem bundleEquiv_analytic :
    ContMDiff (𝓘(ℂ,ChartCoord).prod 𝓘(ℂ)) (𝓘(ℂ,ChartCoord).prod 𝓘(ℂ)) ω
      bundleEquiv := by
  intro z
  let i := HCore.indexAt z.proj
  have hi : z.proj ∈ baseSet i := HCore.mem_baseSet_at z.proj
  let eh := HCore.localTriv i
  let ep := pullbackTriv i.1
  haveI : MemTrivializationAtlas eh := ⟨⟨i,rfl⟩⟩
  apply (ep.contMDiffAt_iff (show bundleEquiv z ∈ ep.source from hi.1)).mpr
  constructor
  · exact Bundle.contMDiffAt_proj HCore.Fiber
  · have h : ContMDiffAt (𝓘(ℂ,ChartCoord).prod 𝓘(ℂ))
        (𝓘(ℂ,ChartCoord).prod 𝓘(ℂ)) ω eh z :=
      eh.contMDiffOn.contMDiffAt (eh.open_source.mem_nhds hi)
    exact h.snd.congr_of_eventuallyEq (Filter.Eventually.of_forall
      (fun w => congrArg Prod.snd (bundleEquiv_localTriv i w)))

theorem bundleEquiv_symm_analytic :
    ContMDiff (𝓘(ℂ,ChartCoord).prod 𝓘(ℂ)) (𝓘(ℂ,ChartCoord).prod 𝓘(ℂ)) ω
      bundleEquiv.symm := by
  intro z
  let i := HCore.indexAt z.proj
  have hi : z.proj ∈ baseSet i := HCore.mem_baseSet_at z.proj
  let eh := HCore.localTriv i
  let ep := pullbackTriv i.1
  haveI : MemTrivializationAtlas eh := ⟨⟨i,rfl⟩⟩
  apply (eh.contMDiffAt_iff (show bundleEquiv.symm z ∈ eh.source from hi)).mpr
  constructor
  · exact Bundle.contMDiffAt_proj PullbackFiber
  · have h : ContMDiffAt (𝓘(ℂ,ChartCoord).prod 𝓘(ℂ))
        (𝓘(ℂ,ChartCoord).prod 𝓘(ℂ)) ω ep z :=
      ep.contMDiffOn.contMDiffAt (ep.open_source.mem_nhds hi.1)
    exact h.snd.congr_of_eventuallyEq (Filter.Eventually.of_forall
      (fun w => congrArg Prod.snd (bundleEquiv_symm_localTriv i w)))

def bundleHomeomorph : HCore.TotalSpace ≃ₜ PullbackTotal where
  toEquiv := bundleEquiv
  continuous_toFun := bundleEquiv_analytic.continuous
  continuous_invFun := bundleEquiv_symm_analytic.continuous

/-- Same base, genuine pullback topology, complex-linear fibres and both
analytic directions. The homogeneous P² degree-one model is the existing one. -/
theorem actual_hyperplane_pullback_certificate :
    ContMDiff (𝓘(ℂ,ChartCoord).prod 𝓘(ℂ)) (𝓘(ℂ,ChartCoord).prod 𝓘(ℂ)) ω bundleHomeomorph ∧
    ContMDiff (𝓘(ℂ,ChartCoord).prod 𝓘(ℂ)) (𝓘(ℂ,ChartCoord).prod 𝓘(ℂ)) ω bundleHomeomorph.symm ∧
    (∀ p v, bundleHomeomorph ⟨p,v⟩ = ⟨p,fibreEquiv p v⟩) ∧
    ∀ i z, pullbackTriv i.1 (bundleHomeomorph z) = HCore.localTriv i z :=
  ⟨bundleEquiv_analytic,bundleEquiv_symm_analytic,fun _ _ => rfl,bundleEquiv_localTriv⟩

end
end FailureOfSemipositiveMetricExtension.GlobalLineBundle.Hyperplane
