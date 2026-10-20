import FailureOfSemipositiveMetricExtension.HisamotoBundleIsomorphism

/-! The bidegree (a,0) incidence bundle is the actual native pullback of O(a)
under the actual projective blowdown, with analytic maps in both directions. -/
namespace FailureOfSemipositiveMetricExtension.Hisamoto.LineBundle
noncomputable section
open Set Bundle Topology
open scoped Manifold ContDiff

variable (a : ℤ)
def blowdownMap : ContMDiffMap 𝓘(ℂ,Coord) 𝓘(ℂ,Coord) Point PlanePoint ω :=
  ⟨blowdown,blowdown_contMDiff ω⟩
abbrev HyperplaneFiber := blowdownMap *ᵖ (ProjectivePlaneBundle.core a).Fiber
abbrev HyperplaneTotal := Bundle.TotalSpace ℂ (HyperplaneFiber a)

def hSourceFrame (f : Frame) (q : Point) (hq : q ∈ baseSet f) : (core a 0).Fiber q ≃L[ℂ] ℂ :=
  (core a 0).localTriv f |>.continuousLinearEquivAt ℂ q hq

def hTargetFrame (f : Frame) (q : Point) (hq : q ∈ baseSet f) : HyperplaneFiber a q ≃L[ℂ] ℂ :=
  (ProjectivePlaneBundle.core a).localTriv (planeIndex f.1 f.2) |>.continuousLinearEquivAt ℂ
    (blowdown q) (planeChart_of_affineChart f.1 f.2 q hq)

theorem hSourceFrame_transition (f g : Frame) (q : Point)
    (hf : q ∈ baseSet f) (hg : q ∈ baseSet g) (v : (core a 0).Fiber q) :
    hSourceFrame a g q hg v = gain a 0 f g q * hSourceFrame a f q hf v := by
  change gain a 0 _ g q * (show ℂ from v) = gain a 0 f g q * (gain a 0 _ f q * (show ℂ from v))
  rw [← mul_assoc]
  exact congrArg (fun z : ℂ => z * (show ℂ from v))
    (gain_comp a 0 ((core a 0).indexAt q) f g q ⟨⟨(core a 0).mem_baseSet_at q,hf⟩,hg⟩).symm

theorem hTargetFrame_transition (f g : Frame) (q : Point)
    (hf : q ∈ baseSet f) (hg : q ∈ baseSet g) (v : HyperplaneFiber a q) :
    hTargetFrame a g q hg v = gain a 0 f g q * hTargetFrame a f q hf v := by
  change ProjectivePlaneBundle.gain a _ (planeIndex g.1 g.2) (blowdown q) * (show ℂ from v) =
    gain a 0 f g q * (ProjectivePlaneBundle.gain a _ (planeIndex f.1 f.2) (blowdown q) * (show ℂ from v))
  simp only [gain,ProjectiveLineBundle.gain,zpow_zero,mul_one]
  rw [← mul_assoc]
  exact congrArg (fun z : ℂ => z * (show ℂ from v))
    (ProjectivePlaneBundle.gain_comp a ((ProjectivePlaneBundle.core a).indexAt (blowdown q))
      (planeIndex f.1 f.2) (planeIndex g.1 g.2) (blowdown q)
      ⟨⟨(ProjectivePlaneBundle.core a).mem_baseSet_at _,planeChart_of_affineChart _ _ q hf⟩,
        planeChart_of_affineChart _ _ q hg⟩).symm

def hyperplaneFiberEquiv (q : Point) : (core a 0).Fiber q ≃L[ℂ] HyperplaneFiber a q :=
  (hSourceFrame a ((core a 0).indexAt q) q ((core a 0).mem_baseSet_at q)).trans
    (hTargetFrame a ((core a 0).indexAt q) q ((core a 0).mem_baseSet_at q)).symm

theorem hyperplaneFiberEquiv_frame (f : Frame) (q : Point) (hq : q ∈ baseSet f)
    (v : (core a 0).Fiber q) :
    hTargetFrame a f q hq (hyperplaneFiberEquiv a q v) = hSourceFrame a f q hq v := by
  let g := (core a 0).indexAt q
  have hg : q ∈ baseSet g := (core a 0).mem_baseSet_at q
  change hTargetFrame a f q hq ((hTargetFrame a g q hg).symm (hSourceFrame a g q hg v)) = _
  rw [hTargetFrame_transition a g f q hg hq,ContinuousLinearEquiv.apply_symm_apply,
    hSourceFrame_transition a g f q hg hq]

def hyperplaneBundleEquiv : (core a 0).TotalSpace ≃ HyperplaneTotal a where
  toFun z := ⟨z.proj,hyperplaneFiberEquiv a z.proj z.2⟩
  invFun z := ⟨z.proj,(hyperplaneFiberEquiv a z.proj).symm z.2⟩
  left_inv z := by cases z; simp
  right_inv z := by cases z; simp

def hyperplaneTriv (f : Frame) : Trivialization ℂ (π ℂ (HyperplaneFiber a)) :=
  ((ProjectivePlaneBundle.core a).localTriv (planeIndex f.1 f.2)).pullback blowdownMap

instance hyperplaneTriv_mem_atlas (f : Frame) : MemTrivializationAtlas (hyperplaneTriv a f) :=
  ⟨⟨(ProjectivePlaneBundle.core a).localTriv (planeIndex f.1 f.2),⟨⟨planeIndex f.1 f.2,rfl⟩⟩,rfl⟩⟩

theorem hyperplaneBundleEquiv_localTriv (f : Frame) (z : (core a 0).TotalSpace)
    (hz : z.proj ∈ baseSet f) :
    hyperplaneTriv a f (hyperplaneBundleEquiv a z) = (core a 0).localTriv f z :=
  Prod.ext rfl (hyperplaneFiberEquiv_frame a f z.proj hz z.2)

theorem hyperplaneBundleEquiv_symm_localTriv (f : Frame) (z : HyperplaneTotal a)
    (hz : z.proj ∈ baseSet f) :
    (core a 0).localTriv f ((hyperplaneBundleEquiv a).symm z) = hyperplaneTriv a f z := by
  have h := hyperplaneBundleEquiv_localTriv a f ((hyperplaneBundleEquiv a).symm z) hz
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

abbrev hyperplaneTotalModel := 𝓘(ℂ,Coord).prod 𝓘(ℂ)

theorem hyperplaneBundleEquiv_contMDiff :
    ContMDiff hyperplaneTotalModel hyperplaneTotalModel ω (hyperplaneBundleEquiv a) := by
  intro z
  let f := (core a 0).indexAt z.proj
  have hf : z.proj ∈ baseSet f := (core a 0).mem_baseSet_at z.proj
  let es := (core a 0).localTriv f
  letI : MemTrivializationAtlas es := ⟨⟨f,rfl⟩⟩
  have ht : hyperplaneBundleEquiv a z ∈ (hyperplaneTriv a f).source :=
    planeChart_of_affineChart _ _ z.proj hf
  apply ((hyperplaneTriv a f).contMDiffAt_iff ht).mpr
  constructor
  · exact Bundle.contMDiffAt_proj (core a 0).Fiber
  · have h : ContMDiffAt hyperplaneTotalModel hyperplaneTotalModel ω es z :=
      es.contMDiffOn.contMDiffAt (es.open_source.mem_nhds hf)
    apply h.snd.congr_of_eventuallyEq
    have hu := ((core a 0).isOpen_baseSet f |>.preimage
      (FiberBundle.continuous_proj ℂ (core a 0).Fiber)).mem_nhds hf
    filter_upwards [hu] with w hw
    exact congrArg Prod.snd (hyperplaneBundleEquiv_localTriv a f w hw)

theorem hyperplaneBundleEquiv_symm_contMDiff :
    ContMDiff hyperplaneTotalModel hyperplaneTotalModel ω (hyperplaneBundleEquiv a).symm := by
  intro z
  let f := (core a 0).indexAt z.proj
  have hf : z.proj ∈ baseSet f := (core a 0).mem_baseSet_at z.proj
  let es := (core a 0).localTriv f
  letI : MemTrivializationAtlas es := ⟨⟨f,rfl⟩⟩
  apply (es.contMDiffAt_iff (show (hyperplaneBundleEquiv a).symm z ∈ es.source from hf)).mpr
  constructor
  · exact Bundle.contMDiffAt_proj (HyperplaneFiber a)
  · have ht : z ∈ (hyperplaneTriv a f).source := planeChart_of_affineChart _ _ z.proj hf
    have h : ContMDiffAt hyperplaneTotalModel hyperplaneTotalModel ω (hyperplaneTriv a f) z :=
      (hyperplaneTriv a f).contMDiffOn.contMDiffAt ((hyperplaneTriv a f).open_source.mem_nhds ht)
    apply h.snd.congr_of_eventuallyEq
    have hu := ((core a 0).isOpen_baseSet f |>.preimage
      (FiberBundle.continuous_proj ℂ (HyperplaneFiber a))).mem_nhds hf
    filter_upwards [hu] with w hw
    exact congrArg Prod.snd (hyperplaneBundleEquiv_symm_localTriv a f w hw)

/-- Actual analytic identification H = blowdown* O(1), and similarly every O(a). -/
def hyperplaneBundleHomeomorph : (core a 0).TotalSpace ≃ₜ HyperplaneTotal a where
  toEquiv := hyperplaneBundleEquiv a
  continuous_toFun := (hyperplaneBundleEquiv_contMDiff a).continuous
  continuous_invFun := (hyperplaneBundleEquiv_symm_contMDiff a).continuous

end
end FailureOfSemipositiveMetricExtension.Hisamoto.LineBundle
