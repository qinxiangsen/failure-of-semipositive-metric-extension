import FailureOfSemipositiveMetricExtension.CentralCurveBundleEquivalence

/-! The two-frame restriction core is connected to the original actual surface
line bundle by an analytic total-space lift that is a continuous complex-linear
isomorphism on each fibre.  This makes the restriction interpretation explicit. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

def restrictionLiftGain (a : ℤ) (b : Fin 4 → ℤ) (d : Direction) : ℂ :=
  gain 0 a b (restrictionFrame ((restrictedCore a b).indexAt d))
    ((core 0 a b).indexAt (lineParam d)) (lineParam d)

def restrictionReturnGain (a : ℤ) (b : Fin 4 → ℤ) (d : Direction) : ℂ :=
  gain 0 a b ((core 0 a b).indexAt (lineParam d))
    (restrictionFrame ((restrictedCore a b).indexAt d)) (lineParam d)

theorem restriction_index_mem (a : ℤ) (b : Fin 4 → ℤ) (d : Direction) :
    lineParam d ∈ baseSet 0 (restrictionFrame ((restrictedCore a b).indexAt d)) :=
  (Set.ext_iff.mp (restrictionFrame_baseSet ((restrictedCore a b).indexAt d)) d).mpr
    ((restrictedCore a b).mem_baseSet_at d)

theorem restrictionReturnGain_mul_liftGain (a : ℤ) (b : Fin 4 → ℤ) (d : Direction) :
    restrictionReturnGain a b d * restrictionLiftGain a b d = 1 := by
  have h := gain_comp 0 a b (restrictionFrame ((restrictedCore a b).indexAt d))
    ((core 0 a b).indexAt (lineParam d)) (restrictionFrame ((restrictedCore a b).indexAt d))
    (lineParam d) ⟨⟨restriction_index_mem a b d,(core 0 a b).mem_baseSet_at (lineParam d)⟩,
      restriction_index_mem a b d⟩
  exact h.trans (gain_self 0 a b _ _)

/-- Actual fibrewise continuous complex-linear identification with the original bundle. -/
def restrictionLiftFiber (a : ℤ) (b : Fin 4 → ℤ) (d : Direction) :
    (restrictedCore a b).Fiber d ≃L[ℂ] (core 0 a b).Fiber (lineParam d) where
  toFun v := restrictionLiftGain a b d * (show ℂ from v)
  invFun v := restrictionReturnGain a b d * (show ℂ from v)
  left_inv v := by
    change restrictionReturnGain a b d * (restrictionLiftGain a b d * (show ℂ from v)) = v
    rw [← mul_assoc,restrictionReturnGain_mul_liftGain,one_mul]
  right_inv v := by
    change restrictionLiftGain a b d * (restrictionReturnGain a b d * (show ℂ from v)) = v
    rw [← mul_assoc,mul_comm (restrictionLiftGain a b d),restrictionReturnGain_mul_liftGain,one_mul]
  map_add' v w := by
    change restrictionLiftGain a b d * ((show ℂ from v) + (show ℂ from w)) = _
    exact mul_add _ _ _
  map_smul' z v := by change _ * (z*(show ℂ from v)) = z*(_*(show ℂ from v)); ring
  continuous_toFun := by
    change Continuous (fun v : ℂ => restrictionLiftGain a b d * v)
    exact continuous_const.mul continuous_id
  continuous_invFun := by
    change Continuous (fun v : ℂ => restrictionReturnGain a b d * v)
    exact continuous_const.mul continuous_id

def restrictionLift (a : ℤ) (b : Fin 4 → ℤ) : (restrictedCore a b).TotalSpace → (core 0 a b).TotalSpace :=
  fun z => ⟨lineParam z.proj,restrictionLiftFiber a b z.proj z.2⟩

@[simp] theorem restrictionLift_projects (a : ℤ) (b : Fin 4 → ℤ) (z : (restrictedCore a b).TotalSpace) :
    (restrictionLift a b z).proj = lineParam z.proj := rfl

theorem restrictionLift_localTriv (a : ℤ) (b : Fin 4 → ℤ) (i : Fin 2)
    (z : (restrictedCore a b).TotalSpace) (hz : z.proj ∈ FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet i) :
    (core 0 a b).localTriv (restrictionFrame i) (restrictionLift a b z) =
      (lineParam z.proj,((restrictedCore a b).localTriv i z).2) := by
  rw [VectorBundleCore.localTriv_apply,VectorBundleCore.localTriv_apply]
  apply Prod.ext
  · rfl
  · change gain 0 a b ((core 0 a b).indexAt (lineParam z.proj)) (restrictionFrame i) (lineParam z.proj) *
      (restrictionLiftGain a b z.proj * (show ℂ from z.2)) =
        gain 0 a b (restrictionFrame ((restrictedCore a b).indexAt z.proj)) (restrictionFrame i) (lineParam z.proj) * (show ℂ from z.2)
    rw [← mul_assoc]
    congr 1
    exact gain_comp 0 a b _ _ _ _ ⟨⟨restriction_index_mem a b z.proj,
      (core 0 a b).mem_baseSet_at (lineParam z.proj)⟩,
      (Set.ext_iff.mp (restrictionFrame_baseSet i) z.proj).mpr hz⟩

theorem restrictionLift_contMDiff (a : ℤ) (b : Fin 4 → ℤ) (n : WithTop ℕ∞) :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) n (restrictionLift a b) := by
  intro z
  let i := (restrictedCore a b).indexAt z.proj
  let er := (restrictedCore a b).localTriv i
  let ea := (core 0 a b).localTriv (restrictionFrame i)
  haveI : MemTrivializationAtlas er := ⟨⟨i,rfl⟩⟩
  haveI : MemTrivializationAtlas ea := ⟨⟨restrictionFrame i,rfl⟩⟩
  have hz : z ∈ er.source := (restrictedCore a b).mem_baseSet_at z.proj
  have hez : restrictionLift a b z ∈ ea.source := restriction_index_mem a b z.proj
  apply (ea.contMDiffAt_iff hez).mpr
  constructor
  · exact (lineParam_contMDiff n).contMDiffAt.comp z
      (Bundle.contMDiffAt_proj (restrictedCore a b).Fiber)
  · have h : ContMDiffAt (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) n er z :=
      er.contMDiffOn.contMDiffAt (er.open_source.mem_nhds hz)
    apply h.snd.congr_of_eventuallyEq
    filter_upwards [er.open_source.mem_nhds hz] with w hw
    exact congrArg Prod.snd (restrictionLift_localTriv a b i w hw)

theorem restrictionLift_injective (a : ℤ) (b : Fin 4 → ℤ) : Function.Injective (restrictionLift a b) := by
  rintro ⟨d,v⟩ ⟨d',w⟩ h
  have hd : d = d' := lineParam_injective (congrArg Bundle.TotalSpace.proj h)
  subst d'
  have hv : restrictionLiftFiber a b d v = restrictionLiftFiber a b d w := by
    injection h
  have hvw := (restrictionLiftFiber a b d).injective hv
  subst w
  rfl

/-- The lift reaches exactly the original bundle fibres over the actual curve. -/
theorem restrictionLift_range (a : ℤ) (b : Fin 4 → ℤ) :
    Set.range (restrictionLift a b) = {z : (core 0 a b).TotalSpace | sectionValue ellSection z.proj = 0} := by
  ext z
  constructor
  · rintro ⟨w,rfl⟩
    exact ellSection_lineParam_zero w.proj
  · intro hz
    obtain ⟨d,hd⟩ := lineParam_surjective_zero z.proj hz
    rcases z with ⟨p,v⟩
    dsimp only at hd
    subst p
    exact ⟨⟨d,(restrictionLiftFiber a b d).symm v⟩,by simp [restrictionLift]⟩

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
