import FailureOfSemipositiveMetricExtension.GenericConicRestrictionFactors

/-! The actual mathlib pullback along the conic parametrization is fibrewise
complex-linearly equivalent to the actual projective-line bundle O(2a + Σ bᵣ).
All comparisons use the original standard pullback topology and actual fibres. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil.Conic
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

def analyticParam (c : Data) : C^ω⟮𝓘(ℂ),Direction;𝓘(ℂ,FixedFiber.Coord),Fiber c.t⟯ :=
  ⟨param c,param_contMDiff c ω⟩

abbrev RestrictedFiber (c : Data) (a : ℤ) (b : Fin 4 → ℤ) :=
  (analyticParam c) *ᵖ (FixedFiberBundle.core c.t a b).Fiber

abbrev RestrictedTotal (c : Data) (a : ℤ) (b : Fin 4 → ℤ) := TotalSpace ℂ (RestrictedFiber c a b)

theorem restricted_analytic (c : Data) (a : ℤ) (b : Fin 4 → ℤ) :
    ContMDiffVectorBundle ω ℂ (RestrictedFiber c a b) 𝓘(ℂ) := inferInstance

theorem restricted_finrank (c : Data) (a : ℤ) (b : Fin 4 → ℤ) (d : Direction) :
    Module.finrank ℂ (RestrictedFiber c a b d) = 1 := Module.finrank_self ℂ

def restrictedTriv (c : Data) (a : ℤ) (b : Fin 4 → ℤ) (i : Frame) :
    Trivialization ℂ (π ℂ (RestrictedFiber c a b)) :=
  ((FixedFiberBundle.core c.t a b).localTriv i).pullback (analyticParam c)

instance restrictedTriv_mem_atlas (c : Data) (a : ℤ) (b : Fin 4 → ℤ) (i : Frame) :
    MemTrivializationAtlas (restrictedTriv c a b i) := by
  haveI : MemTrivializationAtlas ((FixedFiberBundle.core c.t a b).localTriv i) := ⟨⟨i,rfl⟩⟩
  exact ⟨⟨(FixedFiberBundle.core c.t a b).localTriv i,inferInstance,rfl⟩⟩

@[simp] theorem restrictedTriv_baseSet (c : Data) (a : ℤ) (b : Fin 4 → ℤ) (i : Frame) :
    (restrictedTriv c a b i).baseSet = param c ⁻¹' FixedFiberBundle.baseSet c.t i := rfl

def selectedLineFrame (a : ℤ) (b : Fin 4 → ℤ) (d : Direction) : Fin 2 :=
  (ProjectiveLineBundle.core (restrictionDegree a b)).indexAt d

def selectedAmbientFrame (c : Data) (a : ℤ) (b : Fin 4 → ℤ) (d : Direction) : Frame :=
  (FixedFiberBundle.core c.t a b).indexAt (param c d)

theorem selected_patch (c : Data) (a : ℤ) (b : Fin 4 → ℤ) (d : Direction) :
    d ∈ restrictionPatch c (selectedLineFrame a b d) (selectedAmbientFrame c a b d) :=
  ⟨(ProjectiveLineBundle.core (restrictionDegree a b)).mem_baseSet_at d,
   (FixedFiberBundle.core c.t a b).mem_baseSet_at (param c d)⟩

/-- A genuine continuous complex-linear equivalence on every actual fibre. -/
def restrictionFiberEquiv (c : Data) (a : ℤ) (b : Fin 4 → ℤ) (d : Direction) :
    RestrictedFiber c a b d ≃L[ℂ] (ProjectiveLineBundle.core (restrictionDegree a b)).Fiber d where
  toFun v := restrictionFactor c a b (selectedLineFrame a b d) (selectedAmbientFrame c a b d) d * (show ℂ from v)
  invFun v := (restrictionFactor c a b (selectedLineFrame a b d) (selectedAmbientFrame c a b d) d)⁻¹ * (show ℂ from v)
  left_inv v := by
    change _⁻¹ * (_ * (show ℂ from v)) = v
    rw [← mul_assoc,inv_mul_cancel₀ (restrictionFactor_ne_zero c a b _ _ d (selected_patch c a b d)),one_mul]
  right_inv v := by
    change _ * (_⁻¹ * (show ℂ from v)) = v
    rw [← mul_assoc,mul_inv_cancel₀ (restrictionFactor_ne_zero c a b _ _ d (selected_patch c a b d)),one_mul]
  map_add' v w := by change _*((show ℂ from v)+(show ℂ from w)) = _; exact mul_add _ _ _
  map_smul' z v := by change _*(z*(show ℂ from v)) = z*(_*(show ℂ from v)); ring
  continuous_toFun := by change Continuous (fun v : ℂ => _ * v); exact continuous_const.mul continuous_id
  continuous_invFun := by change Continuous (fun v : ℂ => _ * v); exact continuous_const.mul continuous_id

def restrictionBundleEquiv (c : Data) (a : ℤ) (b : Fin 4 → ℤ) :
    RestrictedTotal c a b ≃ (ProjectiveLineBundle.core (restrictionDegree a b)).TotalSpace where
  toFun z := ⟨z.proj,restrictionFiberEquiv c a b z.proj z.2⟩
  invFun z := ⟨z.proj,(restrictionFiberEquiv c a b z.proj).symm z.2⟩
  left_inv z := by cases z; simp
  right_inv z := by cases z; simp

@[simp] theorem restrictionBundleEquiv_projects (c : Data) (a : ℤ) (b : Fin 4 → ℤ)
    (z : RestrictedTotal c a b) : (restrictionBundleEquiv c a b z).proj = z.proj := rfl

@[simp] theorem restrictionBundleEquiv_symm_projects (c : Data) (a : ℤ) (b : Fin 4 → ℤ)
    (z : (ProjectiveLineBundle.core (restrictionDegree a b)).TotalSpace) :
    ((restrictionBundleEquiv c a b).symm z).proj = z.proj := rfl

/-- The full local formula on every member of the verified refined cover. -/
theorem restrictionBundleEquiv_localTriv (c : Data) (a : ℤ) (b : Fin 4 → ℤ)
    (e : Fin 2) (i : Frame) (z : RestrictedTotal c a b) (hz : z.proj ∈ restrictionPatch c e i) :
    (ProjectiveLineBundle.core (restrictionDegree a b)).localTriv e (restrictionBundleEquiv c a b z) =
      (z.proj,restrictionFactor c a b e i z.proj * (restrictedTriv c a b i z).2) := by
  apply Prod.ext
  · rfl
  · change ProjectiveLineBundle.gain (restrictionDegree a b) (selectedLineFrame a b z.proj) e z.proj *
      (restrictionFactor c a b (selectedLineFrame a b z.proj) (selectedAmbientFrame c a b z.proj) z.proj *
        (show ℂ from z.2)) =
      restrictionFactor c a b e i z.proj *
        (FixedFiberBundle.gain c.t a b (selectedAmbientFrame c a b z.proj) i (param c z.proj) *
          (show ℂ from z.2))
    rw [← mul_assoc,← mul_assoc,restrictionFactor_change c a b _ e _ i z.proj (selected_patch c a b z.proj) hz]

theorem restrictionBundleEquiv_symm_localTriv (c : Data) (a : ℤ) (b : Fin 4 → ℤ)
    (e : Fin 2) (i : Frame) (z : (ProjectiveLineBundle.core (restrictionDegree a b)).TotalSpace)
    (hz : z.proj ∈ restrictionPatch c e i) :
    restrictedTriv c a b i ((restrictionBundleEquiv c a b).symm z) =
      (z.proj,(restrictionFactor c a b e i z.proj)⁻¹ *
        ((ProjectiveLineBundle.core (restrictionDegree a b)).localTriv e z).2) := by
  have h := restrictionBundleEquiv_localTriv c a b e i ((restrictionBundleEquiv c a b).symm z) hz
  rw [Equiv.apply_symm_apply] at h
  have hs := congrArg Prod.snd h
  apply Prod.ext
  · rfl
  · rw [hs]
    change _ = (restrictionFactor c a b e i z.proj)⁻¹ *
      (restrictionFactor c a b e i z.proj * (restrictedTriv c a b i ((restrictionBundleEquiv c a b).symm z)).2)
    rw [← mul_assoc,inv_mul_cancel₀ (restrictionFactor_ne_zero c a b e i z.proj hz),one_mul]

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil.Conic
