import FailureOfSemipositiveMetricExtension.HisamotoTensorBundle

namespace FailureOfSemipositiveMetricExtension.Hisamoto.LineBundle
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff TensorProduct

def tensorBundleEquiv : TensorTotal ≃ (core 2 (-1)).TotalSpace where
  toFun z := ⟨z.proj,scalarTensorEquiv z.2⟩
  invFun z := ⟨z.proj,(scalarTensorEquiv).symm z.2⟩
  left_inv z := by cases z; simp
  right_inv z := by cases z; simp

@[simp] theorem tensorBundleEquiv_projects (z : TensorTotal) :
    (tensorBundleEquiv z).proj = z.proj := rfl
@[simp] theorem tensorBundleEquiv_symm_projects (z : (core 2 (-1)).TotalSpace) :
    ((tensorBundleEquiv).symm z).proj = z.proj := rfl

theorem tensorBundleEquiv_localTriv (i : Frame) (z : TensorTotal)
    (hz : z.proj ∈ (core 2 (-1)).baseSet i) :
    (core 2 (-1)).localTriv i (tensorBundleEquiv z) = tensorTriv i z := by
  rcases z with ⟨p,v⟩
  rw [tensorTriv_apply i p hz]
  rfl

theorem tensorBundleEquiv_symm_localTriv (i : Frame) (z : (core 2 (-1)).TotalSpace)
    (hz : z.proj ∈ (core 2 (-1)).baseSet i) :
    tensorTriv i ((tensorBundleEquiv).symm z) = (core 2 (-1)).localTriv i z := by
  have h := tensorBundleEquiv_localTriv i ((tensorBundleEquiv).symm z) hz
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

theorem tensorBundleEquiv_contMDiff :
    ContMDiff (𝓘(ℂ,Coord).prod 𝓘(ℂ)) (𝓘(ℂ,Coord).prod 𝓘(ℂ)) ω
      (tensorBundleEquiv) := by
  intro z
  let i := (core 2 (-1)).indexAt z.proj
  have hp : z.proj ∈ (core 2 (-1)).baseSet i := (core 2 (-1)).mem_baseSet_at z.proj
  let en := tensorTriv i
  let ep := (core 2 (-1)).localTriv i
  letI : MemTrivializationAtlas ep := ⟨⟨i,rfl⟩⟩
  have hep : tensorBundleEquiv z ∈ ep.source := hp
  apply (ep.contMDiffAt_iff hep).mpr
  constructor
  · exact Bundle.contMDiffAt_proj (TensorFiber)
  · have hN : ContMDiffAt (𝓘(ℂ,Coord).prod 𝓘(ℂ)) (𝓘(ℂ,Coord).prod 𝓘(ℂ)) ω en z :=
      en.contMDiffOn.contMDiffAt (en.open_source.mem_nhds hp)
    apply hN.snd.congr_of_eventuallyEq
    have hU := (((core 2 (-1)).isOpen_baseSet i).preimage
      (FiberBundle.continuous_proj ℂ (TensorFiber))).mem_nhds hp
    filter_upwards [hU] with w hw
    exact congrArg Prod.snd (tensorBundleEquiv_localTriv i w hw)

theorem tensorBundleEquiv_symm_contMDiff :
    ContMDiff (𝓘(ℂ,Coord).prod 𝓘(ℂ)) (𝓘(ℂ,Coord).prod 𝓘(ℂ)) ω
      (tensorBundleEquiv).symm := by
  intro z
  let i := (core 2 (-1)).indexAt z.proj
  have hp : z.proj ∈ (core 2 (-1)).baseSet i := (core 2 (-1)).mem_baseSet_at z.proj
  let en := tensorTriv i
  let ep := (core 2 (-1)).localTriv i
  letI : MemTrivializationAtlas ep := ⟨⟨i,rfl⟩⟩
  have hep : z ∈ ep.source := hp
  apply (en.contMDiffAt_iff (show (tensorBundleEquiv).symm z ∈ en.source from hp)).mpr
  constructor
  · exact Bundle.contMDiffAt_proj (core 2 (-1)).Fiber
  · have hP : ContMDiffAt (𝓘(ℂ,Coord).prod 𝓘(ℂ)) (𝓘(ℂ,Coord).prod 𝓘(ℂ)) ω ep z :=
      ep.contMDiffOn.contMDiffAt (ep.open_source.mem_nhds hep)
    apply hP.snd.congr_of_eventuallyEq
    have hU := (((core 2 (-1)).isOpen_baseSet i).preimage
      (FiberBundle.continuous_proj ℂ (core 2 (-1)).Fiber)).mem_nhds hp
    filter_upwards [hU] with w hw
    exact congrArg Prod.snd (tensorBundleEquiv_symm_localTriv i w hw)

/-- The genuine H tensor O(E) bundle is analytically bidegree (2,-1). -/
def tensorBundleHomeomorph : TensorTotal ≃ₜ (core 2 (-1)).TotalSpace where
  toEquiv := tensorBundleEquiv
  continuous_toFun := (tensorBundleEquiv_contMDiff).continuous
  continuous_invFun := (tensorBundleEquiv_symm_contMDiff).continuous

@[simp] theorem tensorBundleHomeomorph_mk (p : Point) (v : TensorFiber p) :
    tensorBundleHomeomorph ⟨p,v⟩ = ⟨p,scalarTensorEquiv v⟩ := rfl

theorem tensorBundleHomeomorph_analytic :
    ContMDiff (𝓘(ℂ,Coord).prod 𝓘(ℂ)) (𝓘(ℂ,Coord).prod 𝓘(ℂ)) ω
      (tensorBundleHomeomorph) ∧
    ContMDiff (𝓘(ℂ,Coord).prod 𝓘(ℂ)) (𝓘(ℂ,Coord).prod 𝓘(ℂ)) ω
      (tensorBundleHomeomorph).symm :=
  ⟨tensorBundleEquiv_contMDiff,tensorBundleEquiv_symm_contMDiff⟩

end
end FailureOfSemipositiveMetricExtension.Hisamoto.LineBundle
