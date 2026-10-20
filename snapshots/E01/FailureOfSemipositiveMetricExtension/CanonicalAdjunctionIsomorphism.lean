import FailureOfSemipositiveMetricExtension.CanonicalAdjunctionPullback

/-! Analyticity of genuine dt-adjunction in both directions, with the standard
pullback topology and its intrinsic contraction semantics retained. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalCanonical
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

theorem adjunctionBundleEquiv_contMDiff (t : ℂ) :
    ContMDiff (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (adjunctionBundleEquiv t) := by
  intro z
  let i := (FixedFiber.canonicalCore t).indexAt z.proj
  have hp : z.proj ∈ FixedFiber.source t i.1 i.2 := (FixedFiber.canonicalCore t).mem_baseSet_at z.proj
  let ec := (FixedFiber.canonicalCore t).localTriv i
  let ep := pullbackTriv t i
  haveI : MemTrivializationAtlas ec := ⟨⟨i,rfl⟩⟩
  apply (ec.contMDiffAt_iff (show adjunctionBundleEquiv t z ∈ ec.source from hp)).mpr
  constructor
  · exact Bundle.contMDiffAt_proj (PullbackFiber t)
  · have hP : ContMDiffAt (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ))
        (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω ep z :=
      ep.contMDiffOn.contMDiffAt (ep.open_source.mem_nhds hp)
    apply hP.snd.congr_of_eventuallyEq
    have hU := ((FixedFiber.source_isOpen t i.1 i.2).preimage
      (FiberBundle.continuous_proj ℂ (PullbackFiber t))).mem_nhds hp
    filter_upwards [hU] with w hw
    exact congrArg Prod.snd (adjunctionBundleEquiv_localTriv t i w hw)

theorem adjunctionBundleEquiv_symm_contMDiff (t : ℂ) :
    ContMDiff (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (adjunctionBundleEquiv t).symm := by
  intro z
  let i := (FixedFiber.canonicalCore t).indexAt z.proj
  have hp : z.proj ∈ FixedFiber.source t i.1 i.2 := (FixedFiber.canonicalCore t).mem_baseSet_at z.proj
  let ec := (FixedFiber.canonicalCore t).localTriv i
  let ep := pullbackTriv t i
  haveI : MemTrivializationAtlas ec := ⟨⟨i,rfl⟩⟩
  apply (ep.contMDiffAt_iff (show (adjunctionBundleEquiv t).symm z ∈ ep.source from hp)).mpr
  constructor
  · exact Bundle.contMDiffAt_proj (FixedFiber.canonicalCore t).Fiber
  · have hC : ContMDiffAt (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ))
        (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω ec z :=
      ec.contMDiffOn.contMDiffAt (ec.open_source.mem_nhds hp)
    apply hC.snd.congr_of_eventuallyEq
    have hU := ((FixedFiber.source_isOpen t i.1 i.2).preimage
      (FiberBundle.continuous_proj ℂ (FixedFiber.canonicalCore t).Fiber)).mem_nhds hp
    filter_upwards [hU] with w hw
    exact congrArg Prod.snd (adjunctionBundleEquiv_symm_localTriv t i w hw)

/-- The actual canonical bundle restricted to a fibre is analytically isomorphic
to its actual cotangent determinant bundle by contraction with dπ = dt. -/
def adjunctionBundleHomeomorph (t : ℂ) : PullbackTotal t ≃ₜ (FixedFiber.canonicalCore t).TotalSpace where
  toEquiv := adjunctionBundleEquiv t
  continuous_toFun := (adjunctionBundleEquiv_contMDiff t).continuous
  continuous_invFun := (adjunctionBundleEquiv_symm_contMDiff t).continuous

theorem adjunctionBundleHomeomorph_analytic (t : ℂ) :
    ContMDiff (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (adjunctionBundleHomeomorph t) ∧
    ContMDiff (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (adjunctionBundleHomeomorph t).symm :=
  ⟨adjunctionBundleEquiv_contMDiff t,adjunctionBundleEquiv_symm_contMDiff t⟩

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalCanonical
