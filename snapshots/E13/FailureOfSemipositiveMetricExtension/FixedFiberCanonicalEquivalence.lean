import FailureOfSemipositiveMetricExtension.FixedFiberCanonicalTransition

/-! A genuine fibrewise complex-linear equivalence between the actual ambient
(1;-1,-1,-1,-1) bundle and the Jacobian canonical bundle of each surface fibre. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

abbrev kCore (t : ℂ) := core t 1 (fun _ => -1)
abbrev jacobianCore (t : ℂ) := FixedFiber.canonicalCore t

def canonicalPatchAt (t : ℂ) (p : Fiber t) : DivisionIndex := Classical.choose (divisionPatch_cover t p)
theorem canonicalPatchAt_mem (t : ℂ) (p : Fiber t) : p ∈ divisionPatch t (canonicalPatchAt t p) :=
  Classical.choose_spec (divisionPatch_cover t p)

def canonicalMultiplier (t : ℂ) (p : Fiber t) : ℂ :=
  FixedFiber.canonicalGain t (divisionChart (canonicalPatchAt t p)) ((jacobianCore t).indexAt p) p *
    canonicalFactor t (canonicalPatchAt t p) p *
      gain t 1 (fun _ => -1) ((kCore t).indexAt p) (divisionFrame (canonicalPatchAt t p)) p

theorem canonicalMultiplier_ne_zero (t : ℂ) (p : Fiber t) : canonicalMultiplier t p ≠ 0 := by
  have hp := canonicalPatchAt_mem t p
  have hg : gain t 1 (fun _ => -1) ((kCore t).indexAt p) (divisionFrame (canonicalPatchAt t p)) p ≠ 0 := by
    have h := gain_comp t 1 (fun _ => -1) ((kCore t).indexAt p) (divisionFrame (canonicalPatchAt t p))
      ((kCore t).indexAt p) p ⟨⟨(kCore t).mem_baseSet_at p,hp.2⟩,(kCore t).mem_baseSet_at p⟩
    exact right_ne_zero_of_mul_eq_one (h.trans (gain_self t 1 (fun _ => -1) _ p))
  exact mul_ne_zero (mul_ne_zero (FixedFiber.canonicalGain_ne_zero t _ _ p hp.1
    ((jacobianCore t).mem_baseSet_at p)) (canonicalFactor_ne_zero t _ p hp)) hg

def canonicalFiberEquiv (t : ℂ) (p : Fiber t) : (kCore t).Fiber p ≃L[ℂ] (jacobianCore t).Fiber p where
  toFun v := canonicalMultiplier t p * (show ℂ from v)
  invFun v := (canonicalMultiplier t p)⁻¹ * (show ℂ from v)
  left_inv v := by change _⁻¹ * (_ * (show ℂ from v)) = v; rw [← mul_assoc,inv_mul_cancel₀ (canonicalMultiplier_ne_zero t p),one_mul]
  right_inv v := by change _ * (_⁻¹ * (show ℂ from v)) = v; rw [← mul_assoc,mul_inv_cancel₀ (canonicalMultiplier_ne_zero t p),one_mul]
  map_add' v w := by change _ * ((show ℂ from v) + (show ℂ from w)) = _; exact mul_add _ _ _
  map_smul' z v := by change _ * (z*(show ℂ from v)) = z*(_*(show ℂ from v)); ring
  continuous_toFun := by change Continuous (fun v : ℂ => canonicalMultiplier t p * v); exact continuous_const.mul continuous_id
  continuous_invFun := by change Continuous (fun v : ℂ => (canonicalMultiplier t p)⁻¹ * v); exact continuous_const.mul continuous_id

def canonicalBundleEquiv (t : ℂ) : (kCore t).TotalSpace ≃ (jacobianCore t).TotalSpace where
  toFun z := ⟨z.proj,canonicalFiberEquiv t z.proj z.2⟩
  invFun z := ⟨z.proj,(canonicalFiberEquiv t z.proj).symm z.2⟩
  left_inv z := by cases z; simp
  right_inv z := by cases z; simp

@[simp] theorem canonicalBundleEquiv_projects (t : ℂ) (z : (kCore t).TotalSpace) :
    (canonicalBundleEquiv t z).proj = z.proj := rfl
@[simp] theorem canonicalBundleEquiv_symm_projects (t : ℂ) (z : (jacobianCore t).TotalSpace) :
    ((canonicalBundleEquiv t).symm z).proj = z.proj := rfl

/-- The total-space equivalence has exactly the verified local two-form factor. -/
theorem canonicalBundleEquiv_localTriv (t : ℂ) (d : DivisionIndex) (z : (kCore t).TotalSpace)
    (hz : z.proj ∈ divisionPatch t d) :
    (jacobianCore t).localTriv (divisionChart d) (canonicalBundleEquiv t z) =
      (z.proj,canonicalFactor t d z.proj * ((kCore t).localTriv (divisionFrame d) z).2) := by
  let p := z.proj
  let c := canonicalPatchAt t p
  have hc : p ∈ divisionPatch t c := canonicalPatchAt_mem t p
  have hk := (jacobianCore t).mem_baseSet_at p
  have ha := (kCore t).mem_baseSet_at p
  rw [VectorBundleCore.localTriv_apply,VectorBundleCore.localTriv_apply]
  apply Prod.ext
  · rfl
  · change FixedFiber.canonicalGain t ((jacobianCore t).indexAt p) (divisionChart d) p *
      (FixedFiber.canonicalGain t (divisionChart c) ((jacobianCore t).indexAt p) p * canonicalFactor t c p *
        gain t 1 (fun _ => -1) ((kCore t).indexAt p) (divisionFrame c) p * (show ℂ from z.2)) =
      canonicalFactor t d p * (gain t 1 (fun _ => -1) ((kCore t).indexAt p) (divisionFrame d) p * (show ℂ from z.2))
    calc
      _ = (FixedFiber.canonicalGain t ((jacobianCore t).indexAt p) (divisionChart d) p *
        FixedFiber.canonicalGain t (divisionChart c) ((jacobianCore t).indexAt p) p) * canonicalFactor t c p *
        gain t 1 (fun _ => -1) ((kCore t).indexAt p) (divisionFrame c) p * (show ℂ from z.2) := by ring
      _ = (FixedFiber.canonicalGain t (divisionChart c) (divisionChart d) p * canonicalFactor t c p) *
        gain t 1 (fun _ => -1) ((kCore t).indexAt p) (divisionFrame c) p * (show ℂ from z.2) := by
          rw [FixedFiber.canonicalGain_comp t (divisionChart c) ((jacobianCore t).indexAt p) (divisionChart d) p hc.1 hk hz.1]
      _ = (gain t 1 (fun _ => -1) (divisionFrame c) (divisionFrame d) p * canonicalFactor t d p) *
        gain t 1 (fun _ => -1) ((kCore t).indexAt p) (divisionFrame c) p * (show ℂ from z.2) := by
          rw [canonicalFactor_transition t c d p hc hz]
      _ = canonicalFactor t d p *
        (gain t 1 (fun _ => -1) (divisionFrame c) (divisionFrame d) p *
          gain t 1 (fun _ => -1) ((kCore t).indexAt p) (divisionFrame c) p) * (show ℂ from z.2) := by ring
      _ = _ := by rw [gain_comp t 1 (fun _ => -1) _ _ _ p ⟨⟨ha,hc.2⟩,hz.2⟩]; ring

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
