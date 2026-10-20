import FailureOfSemipositiveMetricExtension.HisamotoExceptionalDivisor
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-! Genuine binary tensor-product bundle for H ⊗ O(E), with actual tensor
fibres and frame products, analytically identified with incidence bidegree (2,-1). -/
namespace FailureOfSemipositiveMetricExtension.Hisamoto.LineBundle
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff TensorProduct

abbrev ScalarTensor := ℂ ⊗[ℂ] ℂ

def scalarTensorEquiv : ScalarTensor ≃ₗ[ℂ] ℂ := TensorProduct.lid ℂ ℂ
instance scalarTensorNormed : NormedAddCommGroup ScalarTensor :=
  NormedAddCommGroup.induced _ ℂ scalarTensorEquiv.toLinearMap scalarTensorEquiv.injective
instance scalarTensorNormedSpace : NormedSpace ℂ ScalarTensor :=
  NormedSpace.induced ℂ _ ℂ scalarTensorEquiv.toLinearMap
instance scalarTensorFiniteDimensional : FiniteDimensional ℂ ScalarTensor :=
  FiniteDimensional.of_injective scalarTensorEquiv.toLinearMap scalarTensorEquiv.injective

def scalarTensorContinuousEquiv : ScalarTensor ≃L[ℂ] ℂ := scalarTensorEquiv.toContinuousLinearEquiv

abbrev TensorFiber (p : Point) := (core 1 0).Fiber p ⊗[ℂ] (core 1 (-1)).Fiber p
abbrev TensorTotal := Bundle.TotalSpace ℂ TensorFiber

instance tensorFiberNormed (p : Point) : NormedAddCommGroup (TensorFiber p) :=
  inferInstanceAs (NormedAddCommGroup ScalarTensor)
instance tensorFiberNormedSpace (p : Point) : NormedSpace ℂ (TensorFiber p) :=
  inferInstanceAs (NormedSpace ℂ ScalarTensor)
instance tensorFiberFiniteDimensional (p : Point) : FiniteDimensional ℂ (TensorFiber p) :=
  inferInstanceAs (FiniteDimensional ℂ ScalarTensor)

def tensorFrameEquiv (i : Frame) (p : Point) (hp : p ∈ (core 2 (-1)).baseSet i) :
    TensorFiber p ≃L[ℂ] ℂ :=
  (scalarTensorContinuousEquiv).trans ((core 2 (-1)).localTriv i |>.continuousLinearEquivAt ℂ p hp)

@[simp] theorem tensorFrameEquiv_apply (i : Frame) (p : Point) (hp : p ∈ (core 2 (-1)).baseSet i)
    (v : TensorFiber p) :
    tensorFrameEquiv i p hp v = gain 2 (-1) ((core 2 (-1)).indexAt p) i p * scalarTensorEquiv v := rfl

theorem tensorFrameEquiv_transition (i j : Frame) (p : Point)
    (hi : p ∈ (core 2 (-1)).baseSet i) (hj : p ∈ (core 2 (-1)).baseSet j) (v : TensorFiber p) :
    tensorFrameEquiv j p hj v = gain 2 (-1) i j p * tensorFrameEquiv i p hi v := by
  simp only [tensorFrameEquiv_apply]
  rw [← mul_assoc,gain_comp 2 (-1) _ _ _ p ⟨⟨(core 2 (-1)).mem_baseSet_at p,hi⟩,hj⟩]

def tensorPretriv (i : Frame) : Pretrivialization ℂ (π ℂ (TensorFiber)) := by
  classical
  exact
    { toFun := fun z => (z.proj,if h : z.proj ∈ (core 2 (-1)).baseSet i then
        tensorFrameEquiv i z.proj h z.2 else 0)
      invFun := fun z => ⟨z.1,if h : z.1 ∈ (core 2 (-1)).baseSet i then
        (tensorFrameEquiv i z.1 h).symm z.2 else 0⟩
      source := {z | z.proj ∈ (core 2 (-1)).baseSet i}
      target := (core 2 (-1)).baseSet i ×ˢ univ
      map_source' := fun z hz => ⟨hz,mem_univ _⟩
      map_target' := fun z hz => hz.1
      left_inv' := fun z hz => by
        rcases z with ⟨p,v⟩
        simp only [mem_setOf_eq] at hz
        simp only [dif_pos hz,ContinuousLinearEquiv.symm_apply_apply]
      right_inv' := fun z hz => by
        rcases z with ⟨p,v⟩
        simp only [mem_prod,mem_univ,and_true] at hz
        simp only [dif_pos hz,ContinuousLinearEquiv.apply_symm_apply]
      open_target := ((core 2 (-1)).isOpen_baseSet i).prod isOpen_univ
      baseSet := (core 2 (-1)).baseSet i
      open_baseSet := (core 2 (-1)).isOpen_baseSet i
      source_eq := rfl
      target_eq := rfl
      proj_toFun := fun _ _ => rfl }

@[simp] theorem tensorPretriv_baseSet (i : Frame) : (tensorPretriv i).baseSet = (core 2 (-1)).baseSet i := rfl

@[simp] theorem tensorPretriv_apply (i : Frame) (p : Point) (hp : p ∈ (core 2 (-1)).baseSet i)
    (v : TensorFiber p) :
    tensorPretriv i ⟨p,v⟩ = (p,tensorFrameEquiv i p hp v) := by
  classical
  change (p,if h : p ∈ (core 2 (-1)).baseSet i then tensorFrameEquiv i p h v else 0) = _
  simp only [dif_pos hp]

instance tensorPretriv_isLinear (i : Frame) : (tensorPretriv i).IsLinear ℂ where
  linear p hp := by
    simpa only [tensorPretriv_apply i p hp] using (tensorFrameEquiv i p hp).toLinearMap.isLinear

theorem tensorPretriv_symm (i : Frame) (p : Point) (hp : p ∈ (core 2 (-1)).baseSet i) (v : ℂ) :
    (tensorPretriv i).symm p v = (tensorFrameEquiv i p hp).symm v := by
  apply (tensorFrameEquiv i p hp).injective
  have h := congrArg Prod.snd ((tensorPretriv i).apply_mk_symm hp v)
  rw [tensorPretriv_apply i p hp] at h
  exact h.trans (ContinuousLinearEquiv.apply_symm_apply _ _).symm

theorem tensorPretriv_coordChange (i j : Frame) (p : Point)
    (hp : p ∈ (core 2 (-1)).baseSet i ∩ (core 2 (-1)).baseSet j) (v : ℂ) :
    (core 2 (-1)).coordChange i j p v =
      (tensorPretriv j ⟨p,(tensorPretriv i).symm p v⟩).2 := by
  rw [tensorPretriv_symm i p hp.1,tensorPretriv_apply j p hp.2,
    tensorFrameEquiv_transition i j p hp.1 hp.2,ContinuousLinearEquiv.apply_symm_apply]
  rfl

def tensorPrebundle : VectorPrebundle ℂ ℂ (TensorFiber) where
  pretrivializationAtlas := range (tensorPretriv)
  pretrivialization_linear' := by rintro _ ⟨i,rfl⟩; infer_instance
  pretrivializationAt p := tensorPretriv ((core 2 (-1)).indexAt p)
  mem_base_pretrivializationAt p := (core 2 (-1)).mem_baseSet_at p
  pretrivialization_mem_atlas _ := ⟨_,rfl⟩
  exists_coordChange := by
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    exact ⟨(core 2 (-1)).coordChange i j,
      (core 2 (-1)).continuousOn_coordChange i j,tensorPretriv_coordChange i j⟩
  totalSpaceMk_isInducing p := by
    let i := (core 2 (-1)).indexAt p
    have hp : p ∈ (core 2 (-1)).baseSet i := (core 2 (-1)).mem_baseSet_at p
    have h := isInducing_const_prod (x := p) |>.mpr (tensorFrameEquiv i p hp).toHomeomorph.isInducing
    convert h using 1
    funext v
    exact tensorPretriv_apply i p hp v

instance tensorTotal_topologicalSpace : TopologicalSpace (TensorTotal) := (tensorPrebundle).totalSpaceTopology
instance tensorFiberBundle : FiberBundle ℂ (TensorFiber) := (tensorPrebundle).toFiberBundle
instance tensorVectorBundle : VectorBundle ℂ ℂ (TensorFiber) := (tensorPrebundle).toVectorBundle

instance tensorPrebundle_contMDiff : (tensorPrebundle).IsContMDiff 𝓘(ℂ,Coord) ω where
  exists_contMDiffCoordChange := by
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    exact ⟨(core 2 (-1)).coordChange i j,
      VectorBundleCore.IsContMDiff.contMDiffOn_coordChange i j,tensorPretriv_coordChange i j⟩

instance tensorContMDiffVectorBundle : ContMDiffVectorBundle ω ℂ (TensorFiber) 𝓘(ℂ,Coord) :=
  (tensorPrebundle).contMDiffVectorBundle 𝓘(ℂ,Coord)

def tensorTriv (i : Frame) : Trivialization ℂ (π ℂ (TensorFiber)) :=
  (tensorPrebundle).trivializationOfMemPretrivializationAtlas
    (show tensorPretriv i ∈ range (tensorPretriv) from ⟨i,rfl⟩)

instance tensorTriv_mem_atlas (i : Frame) : MemTrivializationAtlas (tensorTriv i) := ⟨⟨tensorPretriv i,⟨i,rfl⟩,rfl⟩⟩

@[simp] theorem tensorTriv_baseSet (i : Frame) : (tensorTriv i).baseSet = (core 2 (-1)).baseSet i := rfl

@[simp] theorem tensorTriv_apply (i : Frame) (p : Point) (hp : p ∈ (core 2 (-1)).baseSet i)
    (v : TensorFiber p) :
    tensorTriv i ⟨p,v⟩ = (p,tensorFrameEquiv i p hp v) := tensorPretriv_apply i p hp v

/-- The native tensor-bundle frames send actual pure tensors to products of
coefficients in the actual H and O(E) frames. -/
theorem tensorTriv_pure (i : Frame) (p : Point) (hp : p ∈ baseSet i)
    (v : (core 1 0).Fiber p) (w : (core 1 (-1)).Fiber p) :
    (tensorTriv i ⟨p,v ⊗ₜ[ℂ] w⟩).2 =
      ((core 1 0).localTriv i ⟨p,v⟩).2 * ((core 1 (-1)).localTriv i ⟨p,w⟩).2 := by
  rw [tensorTriv_apply i p hp,tensorFrameEquiv_apply]
  change gain 2 (-1) ((core 2 (-1)).indexAt p) i p * ((show ℂ from v) * (show ℂ from w)) =
    (gain 1 0 ((core 2 (-1)).indexAt p) i p * (show ℂ from v)) *
      (gain 1 (-1) ((core 2 (-1)).indexAt p) i p * (show ℂ from w))
  rw [← hyperplane_times_exceptional_gain]
  ring

end
end FailureOfSemipositiveMetricExtension.Hisamoto.LineBundle
