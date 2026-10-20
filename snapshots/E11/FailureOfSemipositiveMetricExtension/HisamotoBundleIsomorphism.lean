import FailureOfSemipositiveMetricExtension.HisamotoLineBundle
import Mathlib.Geometry.Manifold.VectorBundle.Pullback

/-! A two-sided analytic isomorphism of actual native pullback total spaces:
the incidence line bundle of bidegree `(a,b)` pulled to a ruling product is
isomorphic to the first-projection pullback of the actual `O(a)` bundle. -/
namespace FailureOfSemipositiveMetricExtension.Hisamoto.LineBundle
noncomputable section
open Set Bundle Topology
open scoped Manifold ContDiff

variable (a b : ℤ) (i : Fin 2)

def productMap : ContMDiffMap productModel 𝓘(ℂ,Coord) (Direction × ℂ) Point ω :=
  ⟨localParam i,localParam_contMDiff i ω⟩

def firstMap : ContMDiffMap productModel 𝓘(ℂ) (Direction × ℂ) Direction ω :=
  ⟨Prod.fst,contMDiff_fst⟩

abbrev SourceFiber := (productMap i) *ᵖ (core a b).Fiber
abbrev TargetFiber := firstMap *ᵖ (ProjectiveLineBundle.core a).Fiber
abbrev SourceTotal := Bundle.TotalSpace ℂ (SourceFiber a b i)
abbrev TargetTotal := Bundle.TotalSpace ℂ (TargetFiber a)

def sourceFrame (j : Fin 2) (q : Direction × ℂ) (hq : q.1 ∈ ProjectiveLine.chartSet j) :
    SourceFiber a b i q ≃L[ℂ] ℂ :=
  ((core a b).localTriv (i,j)).continuousLinearEquivAt ℂ (localParam i q)
    ((localParam_mem_affineChart_iff i j q).mpr hq)

def targetFrame (j : Fin 2) (q : Direction × ℂ) (hq : q.1 ∈ ProjectiveLine.chartSet j) :
    TargetFiber a q ≃L[ℂ] ℂ :=
  ((ProjectiveLineBundle.core a).localTriv j).continuousLinearEquivAt ℂ q.1 hq

@[simp] theorem sourceFrame_apply (j : Fin 2) (q : Direction × ℂ)
    (hq : q.1 ∈ ProjectiveLine.chartSet j) (v : SourceFiber a b i q) :
    sourceFrame a b i j q hq v = gain a b ((core a b).indexAt (localParam i q)) (i,j) (localParam i q) * (show ℂ from v) := rfl

@[simp] theorem targetFrame_apply (j : Fin 2) (q : Direction × ℂ)
    (hq : q.1 ∈ ProjectiveLine.chartSet j) (v : TargetFiber a q) :
    targetFrame a j q hq v = ProjectiveLineBundle.gain a
      ((ProjectiveLineBundle.core a).indexAt q.1) j q.1 * (show ℂ from v) := rfl

set_option maxHeartbeats 1000000 in
theorem sourceFrame_transition (j k : Fin 2) (q : Direction × ℂ)
    (hj : q.1 ∈ ProjectiveLine.chartSet j) (hk : q.1 ∈ ProjectiveLine.chartSet k)
    (v : SourceFiber a b i q) :
    sourceFrame a b i k q hk v = ProjectiveLineBundle.gain a j k q.1 * sourceFrame a b i j q hj v := by
  let f : Frame := (core a b).indexAt (localParam i q)
  have hp : localParam i q ∈ baseSet f := (core a b).mem_baseSet_at (localParam i q)
  have hj' : localParam i q ∈ baseSet (i,j) := (localParam_mem_affineChart_iff i j q).mpr hj
  have hk' : localParam i q ∈ baseSet (i,k) := (localParam_mem_affineChart_iff i k q).mpr hk
  have hc := gain_comp a b f (i,j) (i,k) (localParam i q) ⟨⟨hp,hj'⟩,hk'⟩
  rw [sourceFrame_apply,sourceFrame_apply,← gain_local a b i j k q hk,← mul_assoc]
  exact congrArg (fun z : ℂ => z * (show ℂ from v)) hc.symm

theorem targetFrame_transition (j k : Fin 2) (q : Direction × ℂ)
    (hj : q.1 ∈ ProjectiveLine.chartSet j) (hk : q.1 ∈ ProjectiveLine.chartSet k)
    (v : TargetFiber a q) :
    targetFrame a k q hk v = ProjectiveLineBundle.gain a j k q.1 * targetFrame a j q hj v := by
  rw [targetFrame_apply,targetFrame_apply,← mul_assoc,
    ProjectiveLineBundle.gain_comp a _ _ _ q.1
      ⟨⟨(ProjectiveLineBundle.core a).mem_baseSet_at q.1,hj⟩,hk⟩]

/-- Fibre isomorphism built using actual bundle trivializations. The theorem
below proves it does not depend on the chosen valid fibre chart. -/
def fiberEquiv (q : Direction × ℂ) : SourceFiber a b i q ≃L[ℂ] TargetFiber a q :=
  (sourceFrame a b i ((ProjectiveLineBundle.core a).indexAt q.1) q
    ((ProjectiveLineBundle.core a).mem_baseSet_at q.1)).trans
    (targetFrame a ((ProjectiveLineBundle.core a).indexAt q.1) q
      ((ProjectiveLineBundle.core a).mem_baseSet_at q.1)).symm

theorem fiberEquiv_frame (j : Fin 2) (q : Direction × ℂ)
    (hq : q.1 ∈ ProjectiveLine.chartSet j) (v : SourceFiber a b i q) :
    targetFrame a j q hq (fiberEquiv a b i q v) = sourceFrame a b i j q hq v := by
  let k := (ProjectiveLineBundle.core a).indexAt q.1
  have hk : q.1 ∈ ProjectiveLine.chartSet k := (ProjectiveLineBundle.core a).mem_baseSet_at q.1
  change targetFrame a j q hq ((targetFrame a k q hk).symm (sourceFrame a b i k q hk v)) = _
  rw [targetFrame_transition a k j q hk hq,ContinuousLinearEquiv.apply_symm_apply,
    sourceFrame_transition a b i k j q hk hq]

/-- Genuine inverse functions between the native pullback bundle total spaces. -/
def bundleEquiv : SourceTotal a b i ≃ TargetTotal a where
  toFun z := ⟨z.proj,fiberEquiv a b i z.proj z.2⟩
  invFun z := ⟨z.proj,(fiberEquiv a b i z.proj).symm z.2⟩
  left_inv z := by cases z; simp
  right_inv z := by cases z; simp

def sourceTriv (j : Fin 2) : Trivialization ℂ (π ℂ (SourceFiber a b i)) :=
  ((core a b).localTriv (i,j)).pullback (productMap i)

def targetTriv (j : Fin 2) : Trivialization ℂ (π ℂ (TargetFiber a)) :=
  ((ProjectiveLineBundle.core a).localTriv j).pullback firstMap

instance sourceTriv_mem_atlas (j : Fin 2) : MemTrivializationAtlas (sourceTriv a b i j) :=
  ⟨⟨(core a b).localTriv (i,j),⟨⟨(i,j),rfl⟩⟩,rfl⟩⟩
instance targetTriv_mem_atlas (j : Fin 2) : MemTrivializationAtlas (targetTriv a j) :=
  ⟨⟨(ProjectiveLineBundle.core a).localTriv j,⟨⟨j,rfl⟩⟩,rfl⟩⟩

@[simp] theorem sourceTriv_mem_baseSet (j : Fin 2) (q : Direction × ℂ) :
    q ∈ (sourceTriv a b i j).baseSet ↔ q.1 ∈ ProjectiveLine.chartSet j :=
  localParam_mem_affineChart_iff i j q

@[simp] theorem targetTriv_mem_baseSet (j : Fin 2) (q : Direction × ℂ) :
    q ∈ (targetTriv a j).baseSet ↔ q.1 ∈ ProjectiveLine.chartSet j := Iff.rfl

theorem bundleEquiv_localTriv (j : Fin 2) (z : SourceTotal a b i)
    (hz : z.proj.1 ∈ ProjectiveLine.chartSet j) :
    targetTriv a j (bundleEquiv a b i z) = sourceTriv a b i j z :=
  Prod.ext rfl (fiberEquiv_frame a b i j z.proj hz z.2)

theorem bundleEquiv_symm_localTriv (j : Fin 2) (z : TargetTotal a)
    (hz : z.proj.1 ∈ ProjectiveLine.chartSet j) :
    sourceTriv a b i j ((bundleEquiv a b i).symm z) = targetTriv a j z := by
  have h := bundleEquiv_localTriv a b i j ((bundleEquiv a b i).symm z) hz
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

abbrev totalModel := productModel.prod 𝓘(ℂ)

/-- In every actual bundle chart the identification is the identity, hence analytic. -/
theorem bundleEquiv_contMDiff : ContMDiff totalModel totalModel ω (bundleEquiv a b i) := by
  intro z
  let j := (ProjectiveLineBundle.core a).indexAt z.proj.1
  have hj : z.proj.1 ∈ ProjectiveLine.chartSet j := (ProjectiveLineBundle.core a).mem_baseSet_at _
  have ht : bundleEquiv a b i z ∈ (targetTriv a j).source := hj
  apply ((targetTriv a j).contMDiffAt_iff ht).mpr
  constructor
  · exact Bundle.contMDiffAt_proj (SourceFiber a b i)
  · have hs : z ∈ (sourceTriv a b i j).source :=
      (sourceTriv_mem_baseSet a b i j z.proj).mpr hj
    have h : ContMDiffAt totalModel totalModel ω (sourceTriv a b i j) z :=
      (sourceTriv a b i j).contMDiffOn.contMDiffAt
      ((sourceTriv a b i j).open_source.mem_nhds hs)
    apply h.snd.congr_of_eventuallyEq
    have hu := ((ProjectiveLine.chartSet_isOpen j).preimage
      (continuous_fst.comp (FiberBundle.continuous_proj ℂ (SourceFiber a b i)))).mem_nhds hj
    filter_upwards [hu] with w hw
    exact congrArg Prod.snd (bundleEquiv_localTriv a b i j w hw)

theorem bundleEquiv_symm_contMDiff : ContMDiff totalModel totalModel ω (bundleEquiv a b i).symm := by
  intro z
  let j := (ProjectiveLineBundle.core a).indexAt z.proj.1
  have hj : z.proj.1 ∈ ProjectiveLine.chartSet j := (ProjectiveLineBundle.core a).mem_baseSet_at _
  have ht : (bundleEquiv a b i).symm z ∈ (sourceTriv a b i j).source :=
    (sourceTriv_mem_baseSet a b i j z.proj).mpr hj
  apply ((sourceTriv a b i j).contMDiffAt_iff ht).mpr
  constructor
  · exact Bundle.contMDiffAt_proj (TargetFiber a)
  · have hs : z ∈ (targetTriv a j).source := hj
    have h : ContMDiffAt totalModel totalModel ω (targetTriv a j) z :=
      (targetTriv a j).contMDiffOn.contMDiffAt ((targetTriv a j).open_source.mem_nhds hs)
    apply h.snd.congr_of_eventuallyEq
    have hu := ((ProjectiveLine.chartSet_isOpen j).preimage
      (continuous_fst.comp (FiberBundle.continuous_proj ℂ (TargetFiber a)))).mem_nhds hj
    filter_upwards [hu] with w hw
    exact congrArg Prod.snd (bundleEquiv_symm_localTriv a b i j w hw)

/-- Actual analytic pullback bundle isomorphism for every bidegree. -/
def bundleHomeomorph : SourceTotal a b i ≃ₜ TargetTotal a where
  toEquiv := bundleEquiv a b i
  continuous_toFun := (bundleEquiv_contMDiff a b i).continuous
  continuous_invFun := (bundleEquiv_symm_contMDiff a b i).continuous

/-- The paper's local `O(2)` conclusion on the actual incidence bundle `(2,-1)`. -/
def hisamotoBundleHomeomorph : SourceTotal 2 (-1) i ≃ₜ TargetTotal 2 := bundleHomeomorph 2 (-1) i

end
end FailureOfSemipositiveMetricExtension.Hisamoto.LineBundle
