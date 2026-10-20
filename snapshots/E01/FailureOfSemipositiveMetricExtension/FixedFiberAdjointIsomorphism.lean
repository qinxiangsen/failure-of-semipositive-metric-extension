import FailureOfSemipositiveMetricExtension.FixedFiberAdjointEquivalence

/-! The specific adjoint-bundle identification is analytic in both directions,
base preserving, and complex-linear on every fibre. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

theorem adjointBundleEquiv_symm_localTriv (t : ℂ) (m : ℕ) (d : DivisionIndex)
    (z : (adjointCore t m).TotalSpace) (hz : z.proj ∈ divisionPatch t d) :
    (ambientAdjointCore t m).localTriv (divisionFrame d) ((adjointBundleEquiv t m).symm z) =
      (z.proj,(canonicalFactor t d z.proj)⁻¹ * ((adjointCore t m).localTriv d z).2) := by
  have h := adjointBundleEquiv_localTriv t m d ((adjointBundleEquiv t m).symm z) hz
  rw [Equiv.apply_symm_apply] at h
  apply Prod.ext
  · rfl
  · have hs := congrArg Prod.snd h
    change _ = (canonicalFactor t d z.proj)⁻¹ * _
    rw [hs]
    change _ = (canonicalFactor t d z.proj)⁻¹ * (canonicalFactor t d z.proj * _)
    rw [← mul_assoc,inv_mul_cancel₀ (canonicalFactor_ne_zero t d z.proj hz),one_mul]

theorem adjointBundleEquiv_contMDiff (t : ℂ) (m : ℕ) :
    ContMDiff (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (adjointBundleEquiv t m) := by
  intro z
  let d := canonicalPatchAt t z.proj
  have hp : z.proj ∈ divisionPatch t d := canonicalPatchAt_mem t z.proj
  let ea := (ambientAdjointCore t m).localTriv (divisionFrame d)
  let ec := (adjointCore t m).localTriv d
  haveI : MemTrivializationAtlas ea := ⟨⟨divisionFrame d,rfl⟩⟩
  haveI : MemTrivializationAtlas ec := ⟨⟨d,rfl⟩⟩
  apply (ec.contMDiffAt_iff (show adjointBundleEquiv t m z ∈ ec.source from hp)).mpr
  constructor
  · exact Bundle.contMDiffAt_proj (ambientAdjointCore t m).Fiber
  · have hF := ((canonicalFactor_contMDiffOn t d).contMDiffAt
        ((divisionPatch_isOpen t d).mem_nhds hp)).comp z (Bundle.contMDiffAt_proj (ambientAdjointCore t m).Fiber)
    have hA : ContMDiffAt (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω ea z :=
      ea.contMDiffOn.contMDiffAt (ea.open_source.mem_nhds hp.2)
    apply (hF.smul hA.snd).congr_of_eventuallyEq
    have hU := ((divisionPatch_isOpen t d).preimage (FiberBundle.continuous_proj ℂ (ambientAdjointCore t m).Fiber)).mem_nhds hp
    filter_upwards [hU] with w hw
    exact congrArg Prod.snd (adjointBundleEquiv_localTriv t m d w hw)

theorem adjointBundleEquiv_symm_contMDiff (t : ℂ) (m : ℕ) :
    ContMDiff (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (adjointBundleEquiv t m).symm := by
  intro z
  let d := canonicalPatchAt t z.proj
  have hp : z.proj ∈ divisionPatch t d := canonicalPatchAt_mem t z.proj
  let ea := (ambientAdjointCore t m).localTriv (divisionFrame d)
  let ec := (adjointCore t m).localTriv d
  haveI : MemTrivializationAtlas ea := ⟨⟨divisionFrame d,rfl⟩⟩
  haveI : MemTrivializationAtlas ec := ⟨⟨d,rfl⟩⟩
  apply (ea.contMDiffAt_iff (show (adjointBundleEquiv t m).symm z ∈ ea.source from hp.2)).mpr
  constructor
  · exact Bundle.contMDiffAt_proj (adjointCore t m).Fiber
  · have hinv : ContDiffOn ℂ ω (fun v : ℂ => v⁻¹) {v | v ≠ 0} := contDiffOn_id.inv (fun _ h => h)
    have hf : ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω
        (fun p => (canonicalFactor t d p)⁻¹) (divisionPatch t d) :=
      hinv.contMDiffOn.comp (canonicalFactor_contMDiffOn t d) (fun p hp => canonicalFactor_ne_zero t d p hp)
    have hF := (hf.contMDiffAt ((divisionPatch_isOpen t d).mem_nhds hp)).comp z
      (Bundle.contMDiffAt_proj (adjointCore t m).Fiber)
    have hC : ContMDiffAt (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω ec z :=
      ec.contMDiffOn.contMDiffAt (ec.open_source.mem_nhds hp)
    apply (hF.smul hC.snd).congr_of_eventuallyEq
    have hU := ((divisionPatch_isOpen t d).preimage (FiberBundle.continuous_proj ℂ (adjointCore t m).Fiber)).mem_nhds hp
    filter_upwards [hU] with w hw
    exact congrArg Prod.snd (adjointBundleEquiv_symm_localTriv t m d w hw)

/-- Actual analytic bundle isomorphism for K tensor L^m for every natural m. -/
def adjointBundleHomeomorph (t : ℂ) (m : ℕ) : (ambientAdjointCore t m).TotalSpace ≃ₜ (adjointCore t m).TotalSpace where
  toEquiv := adjointBundleEquiv t m
  continuous_toFun := (adjointBundleEquiv_contMDiff t m).continuous
  continuous_invFun := (adjointBundleEquiv_symm_contMDiff t m).continuous

theorem adjointBundleHomeomorph_analytic (t : ℂ) (m : ℕ) :
    ContMDiff (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (adjointBundleHomeomorph t m) ∧
    ContMDiff (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (adjointBundleHomeomorph t m).symm :=
  ⟨adjointBundleEquiv_contMDiff t m,adjointBundleEquiv_symm_contMDiff t m⟩

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
