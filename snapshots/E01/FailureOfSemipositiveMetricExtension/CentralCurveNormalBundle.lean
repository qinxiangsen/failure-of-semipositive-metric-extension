import FailureOfSemipositiveMetricExtension.CentralCurveNormalQuotient
import Mathlib.Analysis.Normed.Group.Quotient

/-! A genuine analytic normal line bundle with the actual tangent quotient as
each fibre. Its fibre topologies are the standard closed-subspace quotient
topologies. The total-space topology and bundle atlas are constructed from the
verified defining-section derivative frames. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.CurveNormal
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

instance instFiniteDimensionalAmbientTangent (d : Direction) : FiniteDimensional ℂ (AmbientTangent d) :=
  inferInstanceAs (FiniteDimensional ℂ (ℂ × ℂ))

instance instIsClosedTangentImage (d : Direction) : IsClosed (tangentImage d : Set (AmbientTangent d)) :=
  (tangentImage d).closed_of_finiteDimensional

/-- The actual quotient-frame isomorphism is continuous for the standard
quotient topology, by finite dimensionality. -/
def frameContinuousEquiv (i : Index) (d : Direction) (hi : lineParam d ∈ baseSet 0 i) :
    NormalFiber d ≃L[ℂ] ℂ := (frameEquiv i d hi).toContinuousLinearEquiv

abbrev NormalTotal := Bundle.TotalSpace ℂ NormalFiber

def pretriv (i : Fin 2) : Pretrivialization ℂ (π ℂ NormalFiber) := by
  classical
  exact
    { toFun := fun z => (z.proj,if h : z.proj ∈ ProjectiveLine.chartSet i then
        frameEquiv (restrictionFrame i) z.proj
          ((Set.ext_iff.mp (restrictionFrame_baseSet i) z.proj).mpr h) z.2 else 0)
      invFun := fun z => ⟨z.1,if h : z.1 ∈ ProjectiveLine.chartSet i then
        (frameEquiv (restrictionFrame i) z.1
          ((Set.ext_iff.mp (restrictionFrame_baseSet i) z.1).mpr h)).symm z.2 else 0⟩
      source := {z | z.proj ∈ ProjectiveLine.chartSet i}
      target := ProjectiveLine.chartSet i ×ˢ univ
      map_source' := fun z hz => ⟨hz,mem_univ _⟩
      map_target' := fun z hz => hz.1
      left_inv' := fun z hz => by
        rcases z with ⟨d,v⟩
        simp only [mem_setOf_eq] at hz
        simp only [dif_pos hz,LinearEquiv.symm_apply_apply]
      right_inv' := fun z hz => by
        rcases z with ⟨d,v⟩
        simp only [mem_prod,mem_univ,and_true] at hz
        simp only [dif_pos hz,LinearEquiv.apply_symm_apply]
      open_target := (ProjectiveLine.chartSet_isOpen i).prod isOpen_univ
      baseSet := ProjectiveLine.chartSet i
      open_baseSet := ProjectiveLine.chartSet_isOpen i
      source_eq := rfl
      target_eq := rfl
      proj_toFun := fun _ _ => rfl }

@[simp] theorem pretriv_baseSet (i : Fin 2) : (pretriv i).baseSet = ProjectiveLine.chartSet i := rfl

@[simp] theorem pretriv_apply (i : Fin 2) (d : Direction) (hd : d ∈ ProjectiveLine.chartSet i)
    (v : NormalFiber d) :
    pretriv i ⟨d,v⟩ = (d,frameEquiv (restrictionFrame i) d
      ((Set.ext_iff.mp (restrictionFrame_baseSet i) d).mpr hd) v) := by
  classical
  change (d,if h : d ∈ ProjectiveLine.chartSet i then frameEquiv (restrictionFrame i) d
    ((Set.ext_iff.mp (restrictionFrame_baseSet i) d).mpr h) v else 0) = _
  simp only [dif_pos hd]

instance pretriv_isLinear (i : Fin 2) : (pretriv i).IsLinear ℂ where
  linear d hd := by
    simpa only [pretriv_apply i d hd] using
      (frameEquiv (restrictionFrame i) d
        ((Set.ext_iff.mp (restrictionFrame_baseSet i) d).mpr hd)).toLinearMap.isLinear

theorem pretriv_symm (i : Fin 2) (d : Direction) (hd : d ∈ ProjectiveLine.chartSet i) (v : ℂ) :
    (pretriv i).symm d v = (frameEquiv (restrictionFrame i) d
      ((Set.ext_iff.mp (restrictionFrame_baseSet i) d).mpr hd)).symm v := by
  apply (frameEquiv (restrictionFrame i) d
    ((Set.ext_iff.mp (restrictionFrame_baseSet i) d).mpr hd)).injective
  have h := congrArg Prod.snd ((pretriv i).apply_mk_symm hd v)
  rw [pretriv_apply i d hd] at h
  exact h.trans (LinearEquiv.apply_symm_apply _ _).symm

theorem pretriv_coordChange (i j : Fin 2) (d : Direction)
    (hd : d ∈ ProjectiveLine.chartSet i ∩ ProjectiveLine.chartSet j) (v : ℂ) :
    (restrictedCore (-2) ellDegree).coordChange i j d v =
      (pretriv j ⟨d,(pretriv i).symm d v⟩).2 := by
  rw [pretriv_symm i d hd.1,pretriv_apply j d hd.2]
  rw [frameEquiv_transition (restrictionFrame i) (restrictionFrame j) d
    ((Set.ext_iff.mp (restrictionFrame_baseSet i) d).mpr hd.1)
    ((Set.ext_iff.mp (restrictionFrame_baseSet j) d).mpr hd.2),LinearEquiv.apply_symm_apply]
  rfl

def prebundle : VectorPrebundle ℂ ℂ NormalFiber where
  pretrivializationAtlas := range pretriv
  pretrivialization_linear' := by rintro _ ⟨i,rfl⟩; infer_instance
  pretrivializationAt d := pretriv ((restrictedCore (-2) ellDegree).indexAt d)
  mem_base_pretrivializationAt d := (restrictedCore (-2) ellDegree).mem_baseSet_at d
  pretrivialization_mem_atlas _ := ⟨_,rfl⟩
  exists_coordChange := by
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    exact ⟨(restrictedCore (-2) ellDegree).coordChange i j,
      (restrictedCore (-2) ellDegree).continuousOn_coordChange i j,pretriv_coordChange i j⟩
  totalSpaceMk_isInducing d := by
    let i := (restrictedCore (-2) ellDegree).indexAt d
    have hd : d ∈ ProjectiveLine.chartSet i := (restrictedCore (-2) ellDegree).mem_baseSet_at d
    have h := isInducing_const_prod (x := d) |>.mpr
      (frameContinuousEquiv (restrictionFrame i) d
        ((Set.ext_iff.mp (restrictionFrame_baseSet i) d).mpr hd)).toHomeomorph.isInducing
    convert h using 1
    funext v
    exact pretriv_apply i d hd v

instance instTopologicalSpaceNormalTotal : TopologicalSpace NormalTotal := prebundle.totalSpaceTopology
instance instFiberBundleNormal : FiberBundle ℂ NormalFiber := prebundle.toFiberBundle
instance instVectorBundleNormal : VectorBundle ℂ ℂ NormalFiber := prebundle.toVectorBundle

instance prebundle_isContMDiff : prebundle.IsContMDiff 𝓘(ℂ) ω where
  exists_contMDiffCoordChange := by
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    exact ⟨(restrictedCore (-2) ellDegree).coordChange i j,
      VectorBundleCore.IsContMDiff.contMDiffOn_coordChange i j,pretriv_coordChange i j⟩

instance instContMDiffVectorBundleNormal : ContMDiffVectorBundle ω ℂ NormalFiber 𝓘(ℂ) :=
  prebundle.contMDiffVectorBundle 𝓘(ℂ)

def localTriv (i : Fin 2) : Trivialization ℂ (π ℂ NormalFiber) :=
  prebundle.trivializationOfMemPretrivializationAtlas (show pretriv i ∈ range pretriv from ⟨i,rfl⟩)

instance localTriv_mem_atlas (i : Fin 2) : MemTrivializationAtlas (localTriv i) := ⟨⟨pretriv i,⟨i,rfl⟩,rfl⟩⟩

@[simp] theorem localTriv_baseSet (i : Fin 2) : (localTriv i).baseSet = ProjectiveLine.chartSet i := rfl

@[simp] theorem localTriv_apply (i : Fin 2) (d : Direction) (hd : d ∈ ProjectiveLine.chartSet i)
    (v : NormalFiber d) : localTriv i ⟨d,v⟩ =
      (d,frameEquiv (restrictionFrame i) d ((Set.ext_iff.mp (restrictionFrame_baseSet i) d).mpr hd) v) :=
  pretriv_apply i d hd v

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.CurveNormal
