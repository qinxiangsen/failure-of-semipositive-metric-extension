import FailureOfSemipositiveMetricExtension.NearbyPencilPullback

/-! A base-preserving fibrewise complex-linear equivalence from the actual pencil
line bundle to mathlib's actual O(1) pullback. The precise local factor is the
inverse of the chosen nonvanishing pencil coefficient. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil
noncomputable section
open Set Bundle IsManifold Topology
open FixedFiberBundle
open scoped Manifold ContDiff

def selectedCoordinate (t : ℂ) (p : Fiber t) : Fin 2 :=
  (ProjectiveLineBundle.core 1).indexAt (pencilMap t p)

theorem selectedCoordinate_mem (t : ℂ) (p : Fiber t) :
    pencilMap t p ∈ ProjectiveLine.chartSet (selectedCoordinate t p) :=
  (ProjectiveLineBundle.core 1).mem_baseSet_at _

theorem selectedCoordinate_ne_zero (t : ℂ) (ht : t ≠ 0) (p : Fiber t) :
    valueVector t p (selectedCoordinate t p) ≠ 0 :=
  (ProjectiveLine.vectorPoint_mem_chartSet_iff _ _ (valueVector_ne_zero t ht p)).mp
    (selectedCoordinate_mem t p)

/-- The evaluation isomorphism on the true bundle fibres. -/
def pencilFiberEquiv (t : ℂ) (ht : t ≠ 0) (p : Fiber t) :
    (lineCore t).Fiber p ≃L[ℂ] PullbackFiber t ht p where
  toFun v := (valueVector t p (selectedCoordinate t p))⁻¹ * (show ℂ from v)
  invFun v := valueVector t p (selectedCoordinate t p) * (show ℂ from v)
  left_inv v := by
    change _ * (_⁻¹ * (show ℂ from v)) = v
    rw [← mul_assoc,mul_inv_cancel₀ (selectedCoordinate_ne_zero t ht p),one_mul]
  right_inv v := by
    change _⁻¹ * (_ * (show ℂ from v)) = v
    rw [← mul_assoc,inv_mul_cancel₀ (selectedCoordinate_ne_zero t ht p),one_mul]
  map_add' v w := by change _ * ((show ℂ from v)+(show ℂ from w)) = _; exact mul_add _ _ _
  map_smul' z v := by change _*(z*(show ℂ from v)) = z*(_*(show ℂ from v)); ring
  continuous_toFun := by change Continuous (fun v : ℂ => _ * v); exact continuous_const.mul continuous_id
  continuous_invFun := by change Continuous (fun v : ℂ => _ * v); exact continuous_const.mul continuous_id

def pencilBundleEquiv (t : ℂ) (ht : t ≠ 0) : (lineCore t).TotalSpace ≃ PullbackTotal t ht where
  toFun z := ⟨z.proj,pencilFiberEquiv t ht z.proj z.2⟩
  invFun z := ⟨z.proj,(pencilFiberEquiv t ht z.proj).symm z.2⟩
  left_inv z := by cases z; simp
  right_inv z := by cases z; simp

@[simp] theorem pencilBundleEquiv_projects (t : ℂ) (ht : t ≠ 0) (z : (lineCore t).TotalSpace) :
    (pencilBundleEquiv t ht z).proj = z.proj := rfl

@[simp] theorem pencilBundleEquiv_symm_projects (t : ℂ) (ht : t ≠ 0) (z : PullbackTotal t ht) :
    ((pencilBundleEquiv t ht).symm z).proj = z.proj := rfl

/-- Every local coordinate of the bundle equivalence is division by the selected
pencil section, with no unproved compatibility or local-gluing hypothesis. -/
theorem pencilBundleEquiv_localTriv (t : ℂ) (ht : t ≠ 0) (i : Index) (k : Fin 2)
    (z : (lineCore t).TotalSpace) (hi : z.proj ∈ baseSet t i)
    (hk : pencilMap t z.proj ∈ ProjectiveLine.chartSet k) :
    pullbackTriv t ht k (pencilBundleEquiv t ht z) =
      (z.proj,((lineCore t).localTriv i z).2 / (pencilSection t k).coefficient i z.proj) := by
  let p := z.proj
  let j := (lineCore t).indexAt p
  let l := selectedCoordinate t p
  have hj : p ∈ baseSet t j := (lineCore t).mem_baseSet_at p
  have hl : (pencilSection t l).coefficient j p ≠ 0 := selectedCoordinate_ne_zero t ht p
  have hk' : (pencilSection t k).coefficient j p ≠ 0 :=
    (pencilMap_chartSet_iff t ht j k p hj).mp hk
  have hs := (pencilSection t k).compatible j i p ⟨hj,hi⟩
  have hg := lineGain_ne_zero t j i p ⟨hj,hi⟩
  apply Prod.ext
  · rfl
  · change ProjectiveLineBundle.gain 1 l k (pencilMap t p) *
      ((valueVector t p l)⁻¹ * (show ℂ from z.2)) =
        (gain t (-2) (fun _ => 1) j i p * (show ℂ from z.2)) / (pencilSection t k).coefficient i p
    rw [ProjectiveLineBundle.gain,zpow_one,pencilMap_ratio t j l k p hj hl hk']
    change ((pencilSection t l).coefficient j p / (pencilSection t k).coefficient j p) *
      (((pencilSection t l).coefficient j p)⁻¹ * (show ℂ from z.2)) = _
    rw [← hs]
    field_simp
    ring

theorem pencilBundleEquiv_symm_localTriv (t : ℂ) (ht : t ≠ 0) (i : Index) (k : Fin 2)
    (z : PullbackTotal t ht) (hi : z.proj ∈ baseSet t i)
    (hk : pencilMap t z.proj ∈ ProjectiveLine.chartSet k) :
    (lineCore t).localTriv i ((pencilBundleEquiv t ht).symm z) =
      (z.proj,(pencilSection t k).coefficient i z.proj * (pullbackTriv t ht k z).2) := by
  have h := pencilBundleEquiv_localTriv t ht i k ((pencilBundleEquiv t ht).symm z) hi hk
  rw [Equiv.apply_symm_apply] at h
  have hs := congrArg Prod.snd h
  have hn := (pencilMap_chartSet_iff t ht i k z.proj hi).mp hk
  apply Prod.ext
  · rfl
  · rw [hs]
    change _ = (pencilSection t k).coefficient i z.proj *
      (((lineCore t).localTriv i ((pencilBundleEquiv t ht).symm z)).2 /
        (pencilSection t k).coefficient i z.proj)
    rw [mul_div_cancel₀ _ hn]

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil
