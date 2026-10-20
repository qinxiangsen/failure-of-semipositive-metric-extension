import FailureOfSemipositiveMetricExtension.GeneralTensorPowerBundle

/-! Actual global analytic bundle isomorphism from iterated tensor-product
fibres to the analytic power-line bundle used in the all-m obstruction. -/
namespace FailureOfSemipositiveMetricExtension.GeneralCao
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff TensorProduct

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coord (n+1)) M]
    {J : Type} (L : AnalyticLine n (M := M) J) (m : ℕ)
namespace AnalyticLine

def tensorBundleEquiv : L.TensorTotal m ≃ (L.powerCore m).TotalSpace where
  toFun z := ⟨z.proj,L.tensorFiberEquiv m z.proj z.2⟩
  invFun z := ⟨z.proj,(L.tensorFiberEquiv m z.proj).symm z.2⟩
  left_inv z := by cases z; simp
  right_inv z := by cases z; simp

@[simp] theorem tensorBundleEquiv_projects (z : L.TensorTotal m) :
    (L.tensorBundleEquiv m z).proj = z.proj := rfl
@[simp] theorem tensorBundleEquiv_symm_projects (z : (L.powerCore m).TotalSpace) :
    ((L.tensorBundleEquiv m).symm z).proj = z.proj := rfl

theorem tensorBundleEquiv_localTriv (i : J) (z : L.TensorTotal m)
    (hz : z.proj ∈ L.core.baseSet i) :
    (L.powerCore m).localTriv i (L.tensorBundleEquiv m z) = L.tensorTriv m i z := by
  rcases z with ⟨p,v⟩
  rw [L.tensorTriv_apply m i p hz]
  rfl

theorem tensorBundleEquiv_symm_localTriv (i : J) (z : (L.powerCore m).TotalSpace)
    (hz : z.proj ∈ L.core.baseSet i) :
    L.tensorTriv m i ((L.tensorBundleEquiv m).symm z) = (L.powerCore m).localTriv i z := by
  have h := L.tensorBundleEquiv_localTriv m i ((L.tensorBundleEquiv m).symm z) hz
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

theorem tensorBundleEquiv_contMDiff :
    ContMDiff (𝓘(ℂ,Coord (n+1)).prod 𝓘(ℂ)) (𝓘(ℂ,Coord (n+1)).prod 𝓘(ℂ)) ω
      (L.tensorBundleEquiv m) := by
  intro z
  let i := L.core.indexAt z.proj
  have hp : z.proj ∈ L.core.baseSet i := L.core.mem_baseSet_at z.proj
  let en := L.tensorTriv m i
  let ep := (L.powerCore m).localTriv i
  letI : MemTrivializationAtlas ep := ⟨⟨i,rfl⟩⟩
  have hep : L.tensorBundleEquiv m z ∈ ep.source := hp
  apply (ep.contMDiffAt_iff hep).mpr
  constructor
  · exact Bundle.contMDiffAt_proj (L.TensorFiber m)
  · have hN : ContMDiffAt (𝓘(ℂ,Coord (n+1)).prod 𝓘(ℂ)) (𝓘(ℂ,Coord (n+1)).prod 𝓘(ℂ)) ω en z :=
      en.contMDiffOn.contMDiffAt (en.open_source.mem_nhds hp)
    apply hN.snd.congr_of_eventuallyEq
    have hU := ((L.core.isOpen_baseSet i).preimage
      (FiberBundle.continuous_proj ℂ (L.TensorFiber m))).mem_nhds hp
    filter_upwards [hU] with w hw
    exact congrArg Prod.snd (L.tensorBundleEquiv_localTriv m i w hw)

theorem tensorBundleEquiv_symm_contMDiff :
    ContMDiff (𝓘(ℂ,Coord (n+1)).prod 𝓘(ℂ)) (𝓘(ℂ,Coord (n+1)).prod 𝓘(ℂ)) ω
      (L.tensorBundleEquiv m).symm := by
  intro z
  let i := L.core.indexAt z.proj
  have hp : z.proj ∈ L.core.baseSet i := L.core.mem_baseSet_at z.proj
  let en := L.tensorTriv m i
  let ep := (L.powerCore m).localTriv i
  letI : MemTrivializationAtlas ep := ⟨⟨i,rfl⟩⟩
  have hep : z ∈ ep.source := hp
  apply (en.contMDiffAt_iff (show (L.tensorBundleEquiv m).symm z ∈ en.source from hp)).mpr
  constructor
  · exact Bundle.contMDiffAt_proj (L.powerCore m).Fiber
  · have hP : ContMDiffAt (𝓘(ℂ,Coord (n+1)).prod 𝓘(ℂ)) (𝓘(ℂ,Coord (n+1)).prod 𝓘(ℂ)) ω ep z :=
      ep.contMDiffOn.contMDiffAt (ep.open_source.mem_nhds hep)
    apply hP.snd.congr_of_eventuallyEq
    have hU := ((L.core.isOpen_baseSet i).preimage
      (FiberBundle.continuous_proj ℂ (L.powerCore m).Fiber)).mem_nhds hp
    filter_upwards [hU] with w hw
    exact congrArg Prod.snd (L.tensorBundleEquiv_symm_localTriv m i w hw)

/-- An actual two-sided analytic bundle homeomorphism, not just a cocycle
identity. Every fibre of the source is mathlib's genuine tensor product. -/
def tensorBundleHomeomorph : L.TensorTotal m ≃ₜ (L.powerCore m).TotalSpace where
  toEquiv := L.tensorBundleEquiv m
  continuous_toFun := (L.tensorBundleEquiv_contMDiff m).continuous
  continuous_invFun := (L.tensorBundleEquiv_symm_contMDiff m).continuous

@[simp] theorem tensorBundleHomeomorph_mk (p : M) (v : L.TensorFiber m p) :
    L.tensorBundleHomeomorph m ⟨p,v⟩ = ⟨p,L.tensorFiberEquiv m p v⟩ := rfl

theorem tensorBundleHomeomorph_analytic :
    ContMDiff (𝓘(ℂ,Coord (n+1)).prod 𝓘(ℂ)) (𝓘(ℂ,Coord (n+1)).prod 𝓘(ℂ)) ω
      (L.tensorBundleHomeomorph m) ∧
    ContMDiff (𝓘(ℂ,Coord (n+1)).prod 𝓘(ℂ)) (𝓘(ℂ,Coord (n+1)).prod 𝓘(ℂ)) ω
      (L.tensorBundleHomeomorph m).symm :=
  ⟨L.tensorBundleEquiv_contMDiff m,L.tensorBundleEquiv_symm_contMDiff m⟩

end AnalyticLine
end
end FailureOfSemipositiveMetricExtension.GeneralCao
