import FailureOfSemipositiveMetricExtension.FixedFiberCanonicalAdjoint

/-! The actual canonical-times-L^m bundle is identified with its verified ambient
multidegree for every natural m, by the same nowhere-zero canonical top-form
factor. No numerical identification is used in place of the transition proof. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

abbrev ambientAdjointCore (t : ℂ) (m : ℕ) := core t (1-2*(m:ℤ)) (fun _ => (m:ℤ)-1)

theorem ambientAdjoint_gain (t : ℂ) (m : ℕ) (i j : Index) (p : Fiber t)
    (hp : p ∈ baseSet t i ∩ baseSet t j) :
    gain t (1-2*(m:ℤ)) (fun _ => (m:ℤ)-1) i j p =
      gain t 1 (fun _ => -1) i j p * gain t (-2) (fun _ => 1) i j p ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have ha : (1-2*((m+1:ℕ):ℤ)) = (1-2*(m:ℤ))+(-2) := by push_cast; ring
    have hb : (fun _ : Fin 4 => ((m+1:ℕ):ℤ)-1) =
        (fun r : Fin 4 => (fun _ : Fin 4 => (m:ℤ)-1) r + (fun _ : Fin 4 => (1:ℤ)) r) := by
      funext r; push_cast; ring
    rw [ha,hb,gain_add t _ _ _ _ i j p hp,ih,pow_succ,mul_assoc]

/-- The exact corrected canonical tensor transition for every m. -/
theorem adjointFactor_transition (t : ℂ) (m : ℕ) (d c : DivisionIndex) (p : Fiber t)
    (hd : p ∈ divisionPatch t d) (hc : p ∈ divisionPatch t c) :
    adjointGain t m d c p * canonicalFactor t d p =
      gain t (1-2*(m:ℤ)) (fun _ => (m:ℤ)-1) (divisionFrame d) (divisionFrame c) p *
        canonicalFactor t c p := by
  rw [ambientAdjoint_gain t m _ _ p ⟨hd.2,hc.2⟩]
  unfold adjointGain
  calc
    _ = (FixedFiber.canonicalGain t (divisionChart d) (divisionChart c) p * canonicalFactor t d p) *
        gain t (-2) (fun _ => 1) (divisionFrame d) (divisionFrame c) p ^ m := by ring
    _ = _ := by rw [canonicalFactor_transition t d c p hd hc]; ring

def adjointMultiplier (t : ℂ) (m : ℕ) (p : Fiber t) : ℂ :=
  canonicalFactor t (canonicalPatchAt t p) p *
    gain t (1-2*(m:ℤ)) (fun _ => (m:ℤ)-1)
      ((ambientAdjointCore t m).indexAt p) (divisionFrame (canonicalPatchAt t p)) p

theorem adjointMultiplier_ne_zero (t : ℂ) (m : ℕ) (p : Fiber t) : adjointMultiplier t m p ≠ 0 := by
  have hd := canonicalPatchAt_mem t p
  have ha := (ambientAdjointCore t m).mem_baseSet_at p
  have hg := gain_comp t (1-2*(m:ℤ)) (fun _ => (m:ℤ)-1)
    ((ambientAdjointCore t m).indexAt p) (divisionFrame (canonicalPatchAt t p))
    ((ambientAdjointCore t m).indexAt p) p ⟨⟨ha,hd.2⟩,ha⟩
  exact mul_ne_zero (canonicalFactor_ne_zero t _ p hd)
    (right_ne_zero_of_mul_eq_one (hg.trans (gain_self t _ _ _ p)))

def adjointFiberEquiv (t : ℂ) (m : ℕ) (p : Fiber t) :
    (ambientAdjointCore t m).Fiber p ≃L[ℂ] (adjointCore t m).Fiber p where
  toFun v := adjointMultiplier t m p * (show ℂ from v)
  invFun v := (adjointMultiplier t m p)⁻¹ * (show ℂ from v)
  left_inv v := by change _⁻¹ * (_ * (show ℂ from v)) = v; rw [← mul_assoc,inv_mul_cancel₀ (adjointMultiplier_ne_zero t m p),one_mul]
  right_inv v := by change _ * (_⁻¹ * (show ℂ from v)) = v; rw [← mul_assoc,mul_inv_cancel₀ (adjointMultiplier_ne_zero t m p),one_mul]
  map_add' v w := by change _*((show ℂ from v)+(show ℂ from w)) = _; exact mul_add _ _ _
  map_smul' z v := by change _*(z*(show ℂ from v)) = z*(_*(show ℂ from v)); ring
  continuous_toFun := by change Continuous (fun v : ℂ => _ * v); exact continuous_const.mul continuous_id
  continuous_invFun := by change Continuous (fun v : ℂ => _ * v); exact continuous_const.mul continuous_id

def adjointBundleEquiv (t : ℂ) (m : ℕ) : (ambientAdjointCore t m).TotalSpace ≃ (adjointCore t m).TotalSpace where
  toFun z := ⟨z.proj,adjointFiberEquiv t m z.proj z.2⟩
  invFun z := ⟨z.proj,(adjointFiberEquiv t m z.proj).symm z.2⟩
  left_inv z := by cases z; simp
  right_inv z := by cases z; simp

@[simp] theorem adjointBundleEquiv_projects (t : ℂ) (m : ℕ) (z : (ambientAdjointCore t m).TotalSpace) :
    (adjointBundleEquiv t m z).proj = z.proj := rfl

@[simp] theorem adjointBundleEquiv_symm_projects (t : ℂ) (m : ℕ) (z : (adjointCore t m).TotalSpace) :
    ((adjointBundleEquiv t m).symm z).proj = z.proj := rfl

/-- Exact coefficient formula in every actual refined chart. -/
theorem adjointBundleEquiv_localTriv (t : ℂ) (m : ℕ) (d : DivisionIndex)
    (z : (ambientAdjointCore t m).TotalSpace) (hz : z.proj ∈ divisionPatch t d) :
    (adjointCore t m).localTriv d (adjointBundleEquiv t m z) =
      (z.proj,canonicalFactor t d z.proj * ((ambientAdjointCore t m).localTriv (divisionFrame d) z).2) := by
  let p := z.proj
  let c := canonicalPatchAt t p
  have hc : p ∈ divisionPatch t c := canonicalPatchAt_mem t p
  have ha := (ambientAdjointCore t m).mem_baseSet_at p
  apply Prod.ext
  · rfl
  · change adjointGain t m c d p *
      (canonicalFactor t c p * gain t (1-2*(m:ℤ)) (fun _ => (m:ℤ)-1)
        ((ambientAdjointCore t m).indexAt p) (divisionFrame c) p * (show ℂ from z.2)) =
      canonicalFactor t d p * (gain t (1-2*(m:ℤ)) (fun _ => (m:ℤ)-1)
        ((ambientAdjointCore t m).indexAt p) (divisionFrame d) p * (show ℂ from z.2))
    rw [← mul_assoc,← mul_assoc,adjointFactor_transition t m c d p hc hz]
    calc
      _ = canonicalFactor t d p *
        (gain t (1-2*(m:ℤ)) (fun _ => (m:ℤ)-1) (divisionFrame c) (divisionFrame d) p *
          gain t (1-2*(m:ℤ)) (fun _ => (m:ℤ)-1) ((ambientAdjointCore t m).indexAt p) (divisionFrame c) p) *
            (show ℂ from z.2) := by ring
      _ = _ := by rw [gain_comp t _ _ _ _ _ p ⟨⟨ha,hc.2⟩,hz.2⟩]; ring

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
