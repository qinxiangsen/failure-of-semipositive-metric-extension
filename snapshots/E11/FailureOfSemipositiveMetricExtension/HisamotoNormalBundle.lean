import FailureOfSemipositiveMetricExtension.HisamotoNormalQuotient

/-! The actual tangent-quotient normal fibres form a genuine analytic line
bundle. The global ruling differential identifies this bundle, analytically in
both directions, with the actual standard `O(0)` bundle on P¹. -/
namespace FailureOfSemipositiveMetricExtension.Hisamoto.RulingNormal
noncomputable section
open Set Bundle Topology IsManifold
open scoped Manifold ContDiff

variable (i : Fin 2) (t : ℂ)
abbrev NormalTotal := Bundle.TotalSpace ℂ (NormalFiber i t)

def normalPretriv : Pretrivialization ℂ (π ℂ (NormalFiber i t)) where
  toFun z := (z.proj,normalEquiv i t z.proj z.2)
  invFun z := ⟨z.1,(normalEquiv i t z.1).symm z.2⟩
  source := univ
  target := univ
  map_source' _ _ := mem_univ _
  map_target' _ _ := mem_univ _
  left_inv' z _ := by cases z; simp
  right_inv' z _ := by cases z; simp
  open_target := isOpen_univ
  baseSet := univ
  open_baseSet := isOpen_univ
  source_eq := by ext; simp
  target_eq := by ext; simp
  proj_toFun _ _ := rfl

instance normalPretriv_isLinear : (normalPretriv i t).IsLinear ℂ where
  linear p _ := (normalEquiv i t p).toLinearMap.isLinear

theorem normalPretriv_symm (p : Direction) (v : ℂ) :
    (normalPretriv i t).symm p v = (normalEquiv i t p).symm v := by
  apply (normalEquiv i t p).injective
  have h := congrArg Prod.snd ((normalPretriv i t).apply_mk_symm (show p ∈ univ from mem_univ _) v)
  exact h.trans (LinearEquiv.apply_symm_apply _ _).symm

def normalPrebundle : VectorPrebundle ℂ ℂ (NormalFiber i t) where
  pretrivializationAtlas := {normalPretriv i t}
  pretrivialization_linear' := by rintro _ rfl; infer_instance
  pretrivializationAt _ := normalPretriv i t
  mem_base_pretrivializationAt _ := mem_univ _
  pretrivialization_mem_atlas _ := rfl
  exists_coordChange := by
    rintro _ rfl _ rfl
    refine ⟨fun _ => ContinuousLinearMap.id ℂ ℂ,continuousOn_const,?_⟩
    intro p _ v
    change v = normalEquiv i t p ((normalPretriv i t).symm p v)
    rw [normalPretriv_symm,LinearEquiv.apply_symm_apply]
  totalSpaceMk_isInducing p := by
    have h := isInducing_const_prod (x := p) |>.mpr (normalContinuousEquiv i t p).toHomeomorph.isInducing
    exact h

instance normalTotal_topologicalSpace : TopologicalSpace (NormalTotal i t) := (normalPrebundle i t).totalSpaceTopology
instance normalFiberBundle : FiberBundle ℂ (NormalFiber i t) := (normalPrebundle i t).toFiberBundle
instance normalVectorBundle : VectorBundle ℂ ℂ (NormalFiber i t) := (normalPrebundle i t).toVectorBundle

instance normalPrebundle_isContMDiff : (normalPrebundle i t).IsContMDiff 𝓘(ℂ) ω where
  exists_contMDiffCoordChange := by
    rintro _ rfl _ rfl
    refine ⟨fun _ => ContinuousLinearMap.id ℂ ℂ,contMDiffOn_const,?_⟩
    intro p _ v
    change v = normalEquiv i t p ((normalPretriv i t).symm p v)
    rw [normalPretriv_symm,LinearEquiv.apply_symm_apply]

instance normalContMDiffVectorBundle : ContMDiffVectorBundle ω ℂ (NormalFiber i t) 𝓘(ℂ) :=
  (normalPrebundle i t).contMDiffVectorBundle 𝓘(ℂ)

def normalTriv : Trivialization ℂ (π ℂ (NormalFiber i t)) :=
  (normalPrebundle i t).trivializationOfMemPretrivializationAtlas (show normalPretriv i t ∈ {normalPretriv i t} from rfl)

instance normalTriv_mem_atlas : MemTrivializationAtlas (normalTriv i t) :=
  ⟨⟨normalPretriv i t,rfl,rfl⟩⟩

@[simp] theorem normalTriv_apply (z : NormalTotal i t) :
    normalTriv i t z = (z.proj,normalEquiv i t z.proj z.2) := rfl

/-- The target is mathlib's actual zero-degree line bundle core on the quotient P¹. -/
def normalBundleEquiv : NormalTotal i t ≃ (ProjectiveLineBundle.core 0).TotalSpace where
  toFun z := ⟨z.proj,normalEquiv i t z.proj z.2⟩
  invFun z := ⟨z.proj,(normalEquiv i t z.proj).symm z.2⟩
  left_inv z := by cases z; simp
  right_inv z := by cases z; simp

theorem normalBundleEquiv_localTriv (j : Fin 2) (z : NormalTotal i t) :
    (ProjectiveLineBundle.core 0).localTriv j (normalBundleEquiv i t z) = normalTriv i t z := by
  change (z.proj,ProjectiveLineBundle.gain 0 _ j z.proj * normalEquiv i t z.proj z.2) = _
  simp [ProjectiveLineBundle.gain,normalTriv_apply]

theorem normalBundleEquiv_symm_localTriv (j : Fin 2) (z : (ProjectiveLineBundle.core 0).TotalSpace) :
    normalTriv i t ((normalBundleEquiv i t).symm z) = (ProjectiveLineBundle.core 0).localTriv j z := by
  have h := normalBundleEquiv_localTriv i t j ((normalBundleEquiv i t).symm z)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

abbrev normalTotalModel := 𝓘(ℂ).prod 𝓘(ℂ)

theorem normalBundleEquiv_contMDiff :
    ContMDiff normalTotalModel normalTotalModel ω (normalBundleEquiv i t) := by
  intro z
  let j := (ProjectiveLineBundle.core 0).indexAt z.proj
  let ep := (ProjectiveLineBundle.core 0).localTriv j
  letI : MemTrivializationAtlas ep := ⟨⟨j,rfl⟩⟩
  have hj : normalBundleEquiv i t z ∈ ep.source := (ProjectiveLineBundle.core 0).mem_baseSet_at z.proj
  apply (ep.contMDiffAt_iff hj).mpr
  constructor
  · exact Bundle.contMDiffAt_proj (NormalFiber i t)
  · have hn : ContMDiffAt normalTotalModel normalTotalModel ω (normalTriv i t) z :=
      (normalTriv i t).contMDiffOn.contMDiffAt ((normalTriv i t).open_source.mem_nhds (mem_univ _))
    apply hn.snd.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun w => congrArg Prod.snd (normalBundleEquiv_localTriv i t j w))

theorem normalBundleEquiv_symm_contMDiff :
    ContMDiff normalTotalModel normalTotalModel ω (normalBundleEquiv i t).symm := by
  intro z
  let j := (ProjectiveLineBundle.core 0).indexAt z.proj
  let ep := (ProjectiveLineBundle.core 0).localTriv j
  letI : MemTrivializationAtlas ep := ⟨⟨j,rfl⟩⟩
  have hj : z ∈ ep.source := (ProjectiveLineBundle.core 0).mem_baseSet_at z.proj
  apply ((normalTriv i t).contMDiffAt_iff (show (normalBundleEquiv i t).symm z ∈ univ from mem_univ _)).mpr
  constructor
  · exact Bundle.contMDiffAt_proj (ProjectiveLineBundle.core 0).Fiber
  · have hp : ContMDiffAt normalTotalModel normalTotalModel ω ep z :=
      ep.contMDiffOn.contMDiffAt (ep.open_source.mem_nhds hj)
    apply hp.snd.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun w => congrArg Prod.snd (normalBundleEquiv_symm_localTriv i t j w))

/-- The actual tangent-quotient normal line is analytically O(0). -/
def normalBundleHomeomorph : NormalTotal i t ≃ₜ (ProjectiveLineBundle.core 0).TotalSpace where
  toEquiv := normalBundleEquiv i t
  continuous_toFun := (normalBundleEquiv_contMDiff i t).continuous
  continuous_invFun := (normalBundleEquiv_symm_contMDiff i t).continuous

theorem actual_normal_bundle_is_O_zero :
    ContMDiff normalTotalModel normalTotalModel ω (normalBundleHomeomorph i t) ∧
      ContMDiff normalTotalModel normalTotalModel ω (normalBundleHomeomorph i t).symm :=
  ⟨normalBundleEquiv_contMDiff i t,normalBundleEquiv_symm_contMDiff i t⟩

end
end FailureOfSemipositiveMetricExtension.Hisamoto.RulingNormal
