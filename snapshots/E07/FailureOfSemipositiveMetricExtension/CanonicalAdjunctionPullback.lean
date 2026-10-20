import FailureOfSemipositiveMetricExtension.CanonicalAdjunctionEquivalence
import Mathlib.Geometry.Manifold.VectorBundle.Pullback

/-! The genuine canonical dt-adjunction as a map from the standard mathlib
pullback bundle, with exact local coordinates and intrinsic tangent-form semantics. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalCanonical
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

def analyticInclusion (t : ℂ) :
    C^ω⟮𝓘(ℂ,FixedFiber.Coord), Fiber t; 𝓘(ℂ,ChartCoord), Total⟯ :=
  ⟨FixedFiber.inclusion t,FixedFiber.inclusion_contMDiff t ω⟩

abbrev PullbackFiber (t : ℂ) := (analyticInclusion t) *ᵖ canonicalCore.Fiber
abbrev PullbackTotal (t : ℂ) := TotalSpace ℂ (PullbackFiber t)

def pullbackTriv (t : ℂ) (i : Index) : Trivialization ℂ (π ℂ (PullbackFiber t)) :=
  (canonicalCore.localTriv i).pullback (analyticInclusion t)

instance pullbackTriv_mem_atlas (t : ℂ) (i : Index) : MemTrivializationAtlas (pullbackTriv t i) := by
  haveI : MemTrivializationAtlas (canonicalCore.localTriv i) := ⟨⟨i,rfl⟩⟩
  exact ⟨⟨canonicalCore.localTriv i,inferInstance,rfl⟩⟩

@[simp] theorem pullbackTriv_baseSet (t : ℂ) (i : Index) :
    (pullbackTriv t i).baseSet = FixedFiber.source t i.1 i.2 := rfl

theorem pullback_analytic (t : ℂ) :
    ContMDiffVectorBundle ω ℂ (PullbackFiber t) 𝓘(ℂ,FixedFiber.Coord) := inferInstance

/-- The fibre map is defined by actual dt-contraction, conjugated by the verified
identifications with ALL alternating top forms. -/
def adjunctionFiberEquiv (t : ℂ) (p : Fiber t) :
    PullbackFiber t p ≃ₗ[ℂ] (FixedFiber.canonicalCore t).Fiber p :=
  ((canonicalFiberFormEquiv (FixedFiber.inclusion t p)).trans (adjunctionEquiv t p)).trans
    (FixedFiber.canonicalFiberFormEquiv t p).symm

theorem adjunctionFiberEquiv_forms (t : ℂ) (p : Fiber t) (v : PullbackFiber t p) :
    FixedFiber.canonicalFiberFormEquiv t p (adjunctionFiberEquiv t p v) =
      adjunction t p (canonicalFiberFormEquiv (FixedFiber.inclusion t p) v) := by
  change FixedFiber.canonicalFiberFormEquiv t p ((FixedFiber.canonicalFiberFormEquiv t p).symm
    (adjunctionEquiv t p (canonicalFiberFormEquiv (FixedFiber.inclusion t p) v))) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

def adjunctionBundleEquiv (t : ℂ) : PullbackTotal t ≃ (FixedFiber.canonicalCore t).TotalSpace where
  toFun z := ⟨z.proj,adjunctionFiberEquiv t z.proj z.2⟩
  invFun z := ⟨z.proj,(adjunctionFiberEquiv t z.proj).symm z.2⟩
  left_inv z := by cases z; simp
  right_inv z := by cases z; simp

@[simp] theorem adjunctionBundleEquiv_projects (t : ℂ) (z : PullbackTotal t) :
    (adjunctionBundleEquiv t z).proj = z.proj := rfl

@[simp] theorem adjunctionBundleEquiv_symm_projects (t : ℂ)
    (z : (FixedFiber.canonicalCore t).TotalSpace) :
    ((adjunctionBundleEquiv t).symm z).proj = z.proj := rfl

/-- Every adapted chart gives the coefficient identity of genuine dt-adjunction. -/
theorem adjunctionBundleEquiv_localTriv (t : ℂ) (i : Index) (z : PullbackTotal t)
    (hp : z.proj ∈ FixedFiber.source t i.1 i.2) :
    (FixedFiber.canonicalCore t).localTriv i (adjunctionBundleEquiv t z) = pullbackTriv t i z := by
  apply Prod.ext
  · rfl
  · have h := adjunctionFiberEquiv_forms t z.proj z.2
    rw [FixedFiber.canonicalFiberFormEquiv_localTriv t i z.proj _ hp,
      canonicalFiberFormEquiv_localTriv i (FixedFiber.inclusion t z.proj) _ hp,
      map_smul,adjunction_coordinateForm t i.1 i.2 z.proj hp] at h
    exact (smul_left_injective ℂ (FixedFiber.tangentCoordinateForm_ne_zero t i.1 i.2 z.proj hp)) h

theorem adjunctionBundleEquiv_symm_localTriv (t : ℂ) (i : Index)
    (z : (FixedFiber.canonicalCore t).TotalSpace) (hp : z.proj ∈ FixedFiber.source t i.1 i.2) :
    pullbackTriv t i ((adjunctionBundleEquiv t).symm z) = (FixedFiber.canonicalCore t).localTriv i z := by
  have h := adjunctionBundleEquiv_localTriv t i ((adjunctionBundleEquiv t).symm z) hp
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalCanonical
