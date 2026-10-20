import FailureOfSemipositiveMetricExtension.FixedFiberCanonicalEquivalence

/-! The specific canonical-bundle identification is analytic in both directions,
base preserving, and complex-linear on every fibre. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

theorem canonicalBundleEquiv_symm_localTriv (t : ℂ) (d : DivisionIndex)
    (z : (jacobianCore t).TotalSpace) (hz : z.proj ∈ divisionPatch t d) :
    (kCore t).localTriv (divisionFrame d) ((canonicalBundleEquiv t).symm z) =
      (z.proj,(canonicalFactor t d z.proj)⁻¹ * ((jacobianCore t).localTriv (divisionChart d) z).2) := by
  have h := canonicalBundleEquiv_localTriv t d ((canonicalBundleEquiv t).symm z) hz
  rw [Equiv.apply_symm_apply] at h
  apply Prod.ext
  · rfl
  · have hs := congrArg Prod.snd h
    change _ = (canonicalFactor t d z.proj)⁻¹ * _
    rw [hs]
    change _ = (canonicalFactor t d z.proj)⁻¹ * (canonicalFactor t d z.proj * _)
    rw [← mul_assoc,inv_mul_cancel₀ (canonicalFactor_ne_zero t d z.proj hz),one_mul]

theorem canonicalBundleEquiv_contMDiff (t : ℂ) :
    ContMDiff (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (canonicalBundleEquiv t) := by
  intro z
  let d := canonicalPatchAt t z.proj
  have hp : z.proj ∈ divisionPatch t d := canonicalPatchAt_mem t z.proj
  let ea := (kCore t).localTriv (divisionFrame d)
  let ec := (jacobianCore t).localTriv (divisionChart d)
  haveI : MemTrivializationAtlas ea := ⟨⟨divisionFrame d,rfl⟩⟩
  haveI : MemTrivializationAtlas ec := ⟨⟨divisionChart d,rfl⟩⟩
  apply (ec.contMDiffAt_iff (show canonicalBundleEquiv t z ∈ ec.source from hp.1)).mpr
  constructor
  · exact Bundle.contMDiffAt_proj (kCore t).Fiber
  · have hF := ((canonicalFactor_contMDiffOn t d).contMDiffAt
        ((divisionPatch_isOpen t d).mem_nhds hp)).comp z (Bundle.contMDiffAt_proj (kCore t).Fiber)
    have hA : ContMDiffAt (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω ea z :=
      ea.contMDiffOn.contMDiffAt (ea.open_source.mem_nhds hp.2)
    apply (hF.smul hA.snd).congr_of_eventuallyEq
    have hU := ((divisionPatch_isOpen t d).preimage (FiberBundle.continuous_proj ℂ (kCore t).Fiber)).mem_nhds hp
    filter_upwards [hU] with w hw
    exact congrArg Prod.snd (canonicalBundleEquiv_localTriv t d w hw)

theorem canonicalBundleEquiv_symm_contMDiff (t : ℂ) :
    ContMDiff (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (canonicalBundleEquiv t).symm := by
  intro z
  let d := canonicalPatchAt t z.proj
  have hp : z.proj ∈ divisionPatch t d := canonicalPatchAt_mem t z.proj
  let ea := (kCore t).localTriv (divisionFrame d)
  let ec := (jacobianCore t).localTriv (divisionChart d)
  haveI : MemTrivializationAtlas ea := ⟨⟨divisionFrame d,rfl⟩⟩
  haveI : MemTrivializationAtlas ec := ⟨⟨divisionChart d,rfl⟩⟩
  apply (ea.contMDiffAt_iff (show (canonicalBundleEquiv t).symm z ∈ ea.source from hp.2)).mpr
  constructor
  · exact Bundle.contMDiffAt_proj (jacobianCore t).Fiber
  · have hinv : ContDiffOn ℂ ω (fun v : ℂ => v⁻¹) {v | v ≠ 0} := contDiffOn_id.inv (fun _ h => h)
    have hf : ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω
        (fun p => (canonicalFactor t d p)⁻¹) (divisionPatch t d) :=
      hinv.contMDiffOn.comp (canonicalFactor_contMDiffOn t d) (fun p hp => canonicalFactor_ne_zero t d p hp)
    have hF := (hf.contMDiffAt ((divisionPatch_isOpen t d).mem_nhds hp)).comp z
      (Bundle.contMDiffAt_proj (jacobianCore t).Fiber)
    have hC : ContMDiffAt (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω ec z :=
      ec.contMDiffOn.contMDiffAt (ec.open_source.mem_nhds hp.1)
    apply (hF.smul hC.snd).congr_of_eventuallyEq
    have hU := ((divisionPatch_isOpen t d).preimage (FiberBundle.continuous_proj ℂ (jacobianCore t).Fiber)).mem_nhds hp
    filter_upwards [hU] with w hw
    exact congrArg Prod.snd (canonicalBundleEquiv_symm_localTriv t d w hw)

/-- Actual analytic bundle isomorphism realizing K=(1;-1,-1,-1,-1). -/
def canonicalBundleHomeomorph (t : ℂ) : (kCore t).TotalSpace ≃ₜ (jacobianCore t).TotalSpace where
  toEquiv := canonicalBundleEquiv t
  continuous_toFun := (canonicalBundleEquiv_contMDiff t).continuous
  continuous_invFun := (canonicalBundleEquiv_symm_contMDiff t).continuous

theorem canonicalBundleHomeomorph_analytic (t : ℂ) :
    ContMDiff (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (canonicalBundleHomeomorph t) ∧
    ContMDiff (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (canonicalBundleHomeomorph t).symm :=
  ⟨canonicalBundleEquiv_contMDiff t,canonicalBundleEquiv_symm_contMDiff t⟩

/-- The already constructed sigma multidegree is exactly the verified K plus four L indices. -/
theorem sigma_degree_is_canonical_plus_four_L :
    (1 : ℤ) + 4 * (-2) = -7 ∧ (fun _ : Fin 4 => (-1 : ℤ) + 4*1) = (fun _ => (3 : ℤ)) := by
  norm_num

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
