import FailureOfSemipositiveMetricExtension.GeneralTensorPowerWeights

/-! The total space has actual mathlib iterated tensor products as its fibres.
We construct its analytic bundle atlas, rather than merely assigning a name to
an mth-power cocycle. The fibre topology is the unique finite-dimensional
complex vector-space topology, realized by the proved scalar equivalence. -/
namespace FailureOfSemipositiveMetricExtension.GeneralCao
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff TensorProduct

instance scalarTensorNormed (m : ℕ) : NormedAddCommGroup (ScalarTensorPower m) :=
  NormedAddCommGroup.induced _ ℂ (scalarTensorEquiv m).toLinearMap (scalarTensorEquiv m).injective

instance scalarTensorNormedSpace (m : ℕ) : NormedSpace ℂ (ScalarTensorPower m) :=
  NormedSpace.induced ℂ _ ℂ (scalarTensorEquiv m).toLinearMap

instance scalarTensorFiniteDimensional (m : ℕ) : FiniteDimensional ℂ (ScalarTensorPower m) :=
  FiniteDimensional.of_injective (scalarTensorEquiv m).toLinearMap (scalarTensorEquiv m).injective

def scalarTensorContinuousEquiv (m : ℕ) : ScalarTensorPower m ≃L[ℂ] ℂ :=
  (scalarTensorEquiv m).toContinuousLinearEquiv

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coord (n+1)) M]
    {J : Type} (L : AnalyticLine n (M := M) J) (m : ℕ)

namespace AnalyticLine
abbrev TensorFiber (p : M) := TensorPower ℂ m (L.core.Fiber p)
abbrev TensorTotal := Bundle.TotalSpace ℂ (L.TensorFiber m)

instance tensorFiberNormed (p : M) : NormedAddCommGroup (L.TensorFiber m p) :=
  inferInstanceAs (NormedAddCommGroup (ScalarTensorPower m))
instance tensorFiberNormedSpace (p : M) : NormedSpace ℂ (L.TensorFiber m p) :=
  inferInstanceAs (NormedSpace ℂ (ScalarTensorPower m))
instance tensorFiberFiniteDimensional (p : M) : FiniteDimensional ℂ (L.TensorFiber m p) :=
  inferInstanceAs (FiniteDimensional ℂ (ScalarTensorPower m))

def tensorFrameEquiv (i : J) (p : M) (hp : p ∈ L.core.baseSet i) :
    L.TensorFiber m p ≃L[ℂ] ℂ :=
  (scalarTensorContinuousEquiv m).trans ((L.powerCore m).localTriv i |>.continuousLinearEquivAt ℂ p hp)

@[simp] theorem tensorFrameEquiv_apply (i : J) (p : M) (hp : p ∈ L.core.baseSet i)
    (v : L.TensorFiber m p) :
    L.tensorFrameEquiv m i p hp v = L.gain (L.core.indexAt p) i p ^ m * scalarTensorEquiv m v := rfl

theorem tensorFrameEquiv_transition (i j : J) (p : M)
    (hi : p ∈ L.core.baseSet i) (hj : p ∈ L.core.baseSet j) (v : L.TensorFiber m p) :
    L.tensorFrameEquiv m j p hj v = L.gain i j p ^ m * L.tensorFrameEquiv m i p hi v := by
  simp only [tensorFrameEquiv_apply]
  rw [← mul_assoc,← mul_pow,L.gain_comp _ _ _ p ⟨⟨L.core.mem_baseSet_at p,hi⟩,hj⟩]

def tensorPretriv (i : J) : Pretrivialization ℂ (π ℂ (L.TensorFiber m)) := by
  classical
  exact
    { toFun := fun z => (z.proj,if h : z.proj ∈ L.core.baseSet i then
        L.tensorFrameEquiv m i z.proj h z.2 else 0)
      invFun := fun z => ⟨z.1,if h : z.1 ∈ L.core.baseSet i then
        (L.tensorFrameEquiv m i z.1 h).symm z.2 else 0⟩
      source := {z | z.proj ∈ L.core.baseSet i}
      target := L.core.baseSet i ×ˢ univ
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
      open_target := (L.core.isOpen_baseSet i).prod isOpen_univ
      baseSet := L.core.baseSet i
      open_baseSet := L.core.isOpen_baseSet i
      source_eq := rfl
      target_eq := rfl
      proj_toFun := fun _ _ => rfl }

@[simp] theorem tensorPretriv_baseSet (i : J) : (L.tensorPretriv m i).baseSet = L.core.baseSet i := rfl

@[simp] theorem tensorPretriv_apply (i : J) (p : M) (hp : p ∈ L.core.baseSet i)
    (v : L.TensorFiber m p) :
    L.tensorPretriv m i ⟨p,v⟩ = (p,L.tensorFrameEquiv m i p hp v) := by
  classical
  change (p,if h : p ∈ L.core.baseSet i then L.tensorFrameEquiv m i p h v else 0) = _
  simp only [dif_pos hp]

instance tensorPretriv_isLinear (i : J) : (L.tensorPretriv m i).IsLinear ℂ where
  linear p hp := by
    simpa only [tensorPretriv_apply L m i p hp] using (L.tensorFrameEquiv m i p hp).toLinearMap.isLinear

theorem tensorPretriv_symm (i : J) (p : M) (hp : p ∈ L.core.baseSet i) (v : ℂ) :
    (L.tensorPretriv m i).symm p v = (L.tensorFrameEquiv m i p hp).symm v := by
  apply (L.tensorFrameEquiv m i p hp).injective
  have h := congrArg Prod.snd ((L.tensorPretriv m i).apply_mk_symm hp v)
  rw [L.tensorPretriv_apply m i p hp] at h
  exact h.trans (ContinuousLinearEquiv.apply_symm_apply _ _).symm

theorem tensorPretriv_coordChange (i j : J) (p : M)
    (hp : p ∈ L.core.baseSet i ∩ L.core.baseSet j) (v : ℂ) :
    (L.powerCore m).coordChange i j p v =
      (L.tensorPretriv m j ⟨p,(L.tensorPretriv m i).symm p v⟩).2 := by
  rw [L.tensorPretriv_symm m i p hp.1,L.tensorPretriv_apply m j p hp.2,
    L.tensorFrameEquiv_transition m i j p hp.1 hp.2,ContinuousLinearEquiv.apply_symm_apply]
  rfl

def tensorPrebundle : VectorPrebundle ℂ ℂ (L.TensorFiber m) where
  pretrivializationAtlas := range (L.tensorPretriv m)
  pretrivialization_linear' := by rintro _ ⟨i,rfl⟩; infer_instance
  pretrivializationAt p := L.tensorPretriv m (L.core.indexAt p)
  mem_base_pretrivializationAt p := L.core.mem_baseSet_at p
  pretrivialization_mem_atlas _ := ⟨_,rfl⟩
  exists_coordChange := by
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    exact ⟨(L.powerCore m).coordChange i j,
      (L.powerCore m).continuousOn_coordChange i j,L.tensorPretriv_coordChange m i j⟩
  totalSpaceMk_isInducing p := by
    let i := L.core.indexAt p
    have hp : p ∈ L.core.baseSet i := L.core.mem_baseSet_at p
    have h := isInducing_const_prod (x := p) |>.mpr (L.tensorFrameEquiv m i p hp).toHomeomorph.isInducing
    convert h using 1
    funext v
    exact L.tensorPretriv_apply m i p hp v

instance tensorTotal_topologicalSpace : TopologicalSpace (L.TensorTotal m) := (L.tensorPrebundle m).totalSpaceTopology
instance tensorFiberBundle : FiberBundle ℂ (L.TensorFiber m) := (L.tensorPrebundle m).toFiberBundle
instance tensorVectorBundle : VectorBundle ℂ ℂ (L.TensorFiber m) := (L.tensorPrebundle m).toVectorBundle

instance tensorPrebundle_contMDiff : (L.tensorPrebundle m).IsContMDiff 𝓘(ℂ,Coord (n+1)) ω where
  exists_contMDiffCoordChange := by
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    exact ⟨(L.powerCore m).coordChange i j,
      VectorBundleCore.IsContMDiff.contMDiffOn_coordChange i j,L.tensorPretriv_coordChange m i j⟩

instance tensorContMDiffVectorBundle : ContMDiffVectorBundle ω ℂ (L.TensorFiber m) 𝓘(ℂ,Coord (n+1)) :=
  (L.tensorPrebundle m).contMDiffVectorBundle 𝓘(ℂ,Coord (n+1))

def tensorTriv (i : J) : Trivialization ℂ (π ℂ (L.TensorFiber m)) :=
  (L.tensorPrebundle m).trivializationOfMemPretrivializationAtlas
    (show L.tensorPretriv m i ∈ range (L.tensorPretriv m) from ⟨i,rfl⟩)

instance tensorTriv_mem_atlas (i : J) : MemTrivializationAtlas (L.tensorTriv m i) := ⟨⟨L.tensorPretriv m i,⟨i,rfl⟩,rfl⟩⟩

@[simp] theorem tensorTriv_baseSet (i : J) : (L.tensorTriv m i).baseSet = L.core.baseSet i := rfl

@[simp] theorem tensorTriv_apply (i : J) (p : M) (hp : p ∈ L.core.baseSet i)
    (v : L.TensorFiber m p) :
    L.tensorTriv m i ⟨p,v⟩ = (p,L.tensorFrameEquiv m i p hp v) := L.tensorPretriv_apply m i p hp v

/-- True iterated tensor products of vectors have the product of their actual
line-frame coefficients in every tensor-bundle frame. -/
theorem tensorTriv_pure (i : J) (p : M) (hp : p ∈ L.core.baseSet i)
    (v : Fin m → L.core.Fiber p) :
    (L.tensorTriv m i ⟨p,PiTensorProduct.tprod ℂ v⟩).2 =
      ∏ k, (L.core.localTriv i ⟨p,v k⟩).2 := by
  rw [L.tensorTriv_apply m i p hp]
  exact tensor_pure_frame (L := L) m i p v

end AnalyticLine
end
end FailureOfSemipositiveMetricExtension.GeneralCao
