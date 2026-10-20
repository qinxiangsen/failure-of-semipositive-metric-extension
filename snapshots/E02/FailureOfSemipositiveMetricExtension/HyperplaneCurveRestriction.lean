import FailureOfSemipositiveMetricExtension.HyperplaneCurveGeometry
import FailureOfSemipositiveMetricExtension.GlobalFiberLineBundle

/-! Restricting the genuine hyperplane bundle to the genuine hyperplane curve.
The actual standard pullback is analytically and fibrewise complex-linearly
isomorphic to O(a), including H|H ≃ O(1). No numerical degree identification
or intersection-theory assertion is used. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.HyperplaneCurve
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

abbrev RestrictionFrame := Fin 2 × (Fin 4 → Fin 2)

def ambientFrame (f : RestrictionFrame) : FixedFiberBundle.Index := (f.1.castSucc,f.2)

def analyticParam (c : Data) : C^ω⟮𝓘(ℂ),Direction;𝓘(ℂ,FixedFiber.Coord),Fiber c.t⟯ :=
  ⟨param c,param_contMDiff c ω⟩

abbrev RestrictedFiber (c : Data) (a : ℤ) :=
  (analyticParam c) *ᵖ (FixedFiberBundle.core c.t a (fun _ => 0)).Fiber
abbrev RestrictedTotal (c : Data) (a : ℤ) := TotalSpace ℂ (RestrictedFiber c a)

theorem restricted_analytic (c : Data) (a : ℤ) :
    ContMDiffVectorBundle ω ℂ (RestrictedFiber c a) 𝓘(ℂ) := inferInstance

theorem restricted_finrank (c : Data) (a : ℤ) (d : Direction) :
    Module.finrank ℂ (RestrictedFiber c a d) = 1 := Module.finrank_self ℂ

theorem base_mem_chart (i : Fin 2) (d : Direction)
    (hd : d ∈ ProjectiveLine.chartSet i) : base d ∈ ProjectivePlane.chartSet i.castSucc := by
  rw [← ProjectiveLine.param_coordinates i d hd,base_param]
  exact ProjectivePlane.param_mem_chartSet _ _

theorem base_ratio (i j : Fin 2) (d : Direction)
    (hd : d ∈ ProjectiveLine.chartSet j) :
    ProjectivePlaneBundle.ratio i.castSucc j.castSucc (base d) = ProjectiveLineBundle.ratio i j d := by
  rw [← ProjectiveLine.param_coordinates j d hd,base_param]
  unfold ProjectivePlaneBundle.ratio ProjectiveLineBundle.ratio
  rw [ProjectivePlane.coordinates_param,ProjectiveLine.coordinates_param]
  fin_cases i <;> fin_cases j <;> simp [ProjectivePlane.vector]

/-- The true fixed-fibre H cocycle is independent of all four direction frames. -/
theorem restriction_gain (c : Data) (a : ℤ) (f g : RestrictionFrame) (d : Direction)
    (hd : d ∈ ProjectiveLine.chartSet g.1) :
    FixedFiberBundle.gain c.t a (fun _ => 0) (ambientFrame f) (ambientFrame g) (param c d) =
      ProjectiveLineBundle.gain a f.1 g.1 d := by
  simp only [FixedFiberBundle.gain,FailureOfSemipositiveMetricExtension.GlobalLineBundle.gain,
    ProjectiveLineBundle.gain,zpow_zero,Finset.prod_const_one,mul_one]
  change ProjectivePlaneBundle.ratio f.1.castSucc g.1.castSucc (base d) ^ a = _
  rw [base_ratio f.1 g.1 d hd]

def restrictionPatch (c : Data) (f : RestrictionFrame) : Set Direction :=
  ProjectiveLine.chartSet f.1 ∩ param c ⁻¹' FixedFiberBundle.baseSet c.t (ambientFrame f)

theorem restrictionPatch_isOpen (c : Data) (f : RestrictionFrame) :
    IsOpen (restrictionPatch c f) :=
  (ProjectiveLine.chartSet_isOpen f.1).inter
    ((FixedFiberBundle.baseSet_isOpen c.t (ambientFrame f)).preimage (param_contMDiff c 0).continuous)

def selectedFrame (c : Data) (a : ℤ) (d : Direction) : RestrictionFrame :=
  ((ProjectiveLineBundle.core a).indexAt d,
    fun r => (ProjectiveLineBundle.core 0).indexAt (direction c r d))

theorem selectedFrame_mem (c : Data) (a : ℤ) (d : Direction) :
    d ∈ restrictionPatch c (selectedFrame c a d) := by
  have hd := (ProjectiveLineBundle.core a).mem_baseSet_at d
  refine ⟨hd,base_mem_chart _ d hd,?_⟩
  intro r
  exact (ProjectiveLineBundle.core 0).mem_baseSet_at (direction c r d)

def restrictedTriv (c : Data) (a : ℤ) (f : RestrictionFrame) :
    Trivialization ℂ (π ℂ (RestrictedFiber c a)) :=
  ((FixedFiberBundle.core c.t a (fun _ => 0)).localTriv (ambientFrame f)).pullback (analyticParam c)

instance restrictedTriv_mem_atlas (c : Data) (a : ℤ) (f : RestrictionFrame) :
    MemTrivializationAtlas (restrictedTriv c a f) := by
  haveI : MemTrivializationAtlas ((FixedFiberBundle.core c.t a (fun _ => 0)).localTriv (ambientFrame f)) :=
    ⟨⟨ambientFrame f,rfl⟩⟩
  exact ⟨⟨(FixedFiberBundle.core c.t a (fun _ => 0)).localTriv (ambientFrame f),inferInstance,rfl⟩⟩

def sourceFrame (c : Data) (a : ℤ) (f : RestrictionFrame) (d : Direction)
    (hd : d ∈ restrictionPatch c f) : RestrictedFiber c a d ≃L[ℂ] ℂ :=
  (FixedFiberBundle.core c.t a (fun _ => 0)).localTriv (ambientFrame f) |>.continuousLinearEquivAt ℂ (param c d) hd.2

def targetFrame (a : ℤ) (f : RestrictionFrame) (d : Direction)
    (hd : d ∈ ProjectiveLine.chartSet f.1) : (ProjectiveLineBundle.core a).Fiber d ≃L[ℂ] ℂ :=
  (ProjectiveLineBundle.core a).localTriv f.1 |>.continuousLinearEquivAt ℂ d hd

theorem sourceFrame_transition (c : Data) (a : ℤ) (f g : RestrictionFrame) (d : Direction)
    (hf : d ∈ restrictionPatch c f) (hg : d ∈ restrictionPatch c g) (v : RestrictedFiber c a d) :
    sourceFrame c a g d hg v = ProjectiveLineBundle.gain a f.1 g.1 d * sourceFrame c a f d hf v := by
  rw [← restriction_gain c a f g d hg.1]
  change FixedFiberBundle.gain c.t a (fun _ => 0) _ (ambientFrame g) (param c d) * (show ℂ from v) =
    _ * (FixedFiberBundle.gain c.t a (fun _ => 0) _ (ambientFrame f) (param c d) * (show ℂ from v))
  rw [← mul_assoc]
  exact congrArg (fun z : ℂ => z * (show ℂ from v))
    (FixedFiberBundle.gain_comp c.t a (fun _ => 0)
      ((FixedFiberBundle.core c.t a (fun _ => 0)).indexAt (param c d))
      (ambientFrame f) (ambientFrame g) (param c d)
      ⟨⟨(FixedFiberBundle.core c.t a (fun _ => 0)).mem_baseSet_at _,hf.2⟩,hg.2⟩).symm

theorem targetFrame_transition (a : ℤ) (f g : RestrictionFrame) (d : Direction)
    (hf : d ∈ ProjectiveLine.chartSet f.1) (hg : d ∈ ProjectiveLine.chartSet g.1)
    (v : (ProjectiveLineBundle.core a).Fiber d) :
    targetFrame a g d hg v = ProjectiveLineBundle.gain a f.1 g.1 d * targetFrame a f d hf v := by
  change ProjectiveLineBundle.gain a _ g.1 d * (show ℂ from v) =
    _ * (ProjectiveLineBundle.gain a _ f.1 d * (show ℂ from v))
  rw [← mul_assoc]
  exact congrArg (fun z : ℂ => z * (show ℂ from v))
    (ProjectiveLineBundle.gain_comp a ((ProjectiveLineBundle.core a).indexAt d) f.1 g.1 d
      ⟨⟨(ProjectiveLineBundle.core a).mem_baseSet_at d,hf⟩,hg⟩).symm

/-- A continuous complex-linear equivalence of the actual fibres, using local
frames selected separately at each point; no global direction chart is assumed. -/
def restrictionFiberEquiv (c : Data) (a : ℤ) (d : Direction) :
    RestrictedFiber c a d ≃L[ℂ] (ProjectiveLineBundle.core a).Fiber d :=
  (sourceFrame c a (selectedFrame c a d) d (selectedFrame_mem c a d)).trans
    (targetFrame a (selectedFrame c a d) d (selectedFrame_mem c a d).1).symm

theorem restrictionFiberEquiv_frame (c : Data) (a : ℤ) (f : RestrictionFrame)
    (d : Direction) (hd : d ∈ restrictionPatch c f) (v : RestrictedFiber c a d) :
    targetFrame a f d hd.1 (restrictionFiberEquiv c a d v) = sourceFrame c a f d hd v := by
  let g := selectedFrame c a d
  have hg : d ∈ restrictionPatch c g := selectedFrame_mem c a d
  change targetFrame a f d hd.1 ((targetFrame a g d hg.1).symm (sourceFrame c a g d hg v)) = _
  rw [targetFrame_transition a g f d hg.1 hd.1,ContinuousLinearEquiv.apply_symm_apply,
    sourceFrame_transition c a g f d hg hd]

def restrictionBundleEquiv (c : Data) (a : ℤ) :
    RestrictedTotal c a ≃ (ProjectiveLineBundle.core a).TotalSpace where
  toFun z := ⟨z.proj,restrictionFiberEquiv c a z.proj z.2⟩
  invFun z := ⟨z.proj,(restrictionFiberEquiv c a z.proj).symm z.2⟩
  left_inv z := by cases z; simp
  right_inv z := by cases z; simp

@[simp] theorem restrictionBundleEquiv_projects (c : Data) (a : ℤ) (z : RestrictedTotal c a) :
    (restrictionBundleEquiv c a z).proj = z.proj := rfl

@[simp] theorem restrictionBundleEquiv_symm_projects (c : Data) (a : ℤ)
    (z : (ProjectiveLineBundle.core a).TotalSpace) :
    ((restrictionBundleEquiv c a).symm z).proj = z.proj := rfl

theorem restrictionBundleEquiv_localTriv (c : Data) (a : ℤ) (f : RestrictionFrame)
    (z : RestrictedTotal c a) (hz : z.proj ∈ restrictionPatch c f) :
    (ProjectiveLineBundle.core a).localTriv f.1 (restrictionBundleEquiv c a z) = restrictedTriv c a f z :=
  Prod.ext rfl (restrictionFiberEquiv_frame c a f z.proj hz z.2)

theorem restrictionBundleEquiv_symm_localTriv (c : Data) (a : ℤ) (f : RestrictionFrame)
    (z : (ProjectiveLineBundle.core a).TotalSpace) (hz : z.proj ∈ restrictionPatch c f) :
    restrictedTriv c a f ((restrictionBundleEquiv c a).symm z) =
      (ProjectiveLineBundle.core a).localTriv f.1 z := by
  have h := restrictionBundleEquiv_localTriv c a f ((restrictionBundleEquiv c a).symm z) hz
  rw [Equiv.apply_symm_apply] at h
  exact h.symm


/-- The comparison is analytic for the original native pullback topology. -/
theorem restrictionBundleEquiv_contMDiff (c : Data) (a : ℤ) :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω (restrictionBundleEquiv c a) := by
  intro z
  let f := selectedFrame c a z.proj
  have hf : z.proj ∈ restrictionPatch c f := selectedFrame_mem c a z.proj
  let el := (ProjectiveLineBundle.core a).localTriv f.1
  let er := restrictedTriv c a f
  haveI : MemTrivializationAtlas el := ⟨⟨f.1,rfl⟩⟩
  apply (el.contMDiffAt_iff (show restrictionBundleEquiv c a z ∈ el.source from hf.1)).mpr
  constructor
  · exact Bundle.contMDiffAt_proj (RestrictedFiber c a)
  · have hR : ContMDiffAt (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω er z :=
      er.contMDiffOn.contMDiffAt (er.open_source.mem_nhds hf.2)
    apply hR.snd.congr_of_eventuallyEq
    have hU := ((restrictionPatch_isOpen c f).preimage
      (FiberBundle.continuous_proj ℂ (RestrictedFiber c a))).mem_nhds hf
    filter_upwards [hU] with w hw
    exact congrArg Prod.snd (restrictionBundleEquiv_localTriv c a f w hw)

/-- The inverse comparison is analytic in the same native bundle structures. -/
theorem restrictionBundleEquiv_symm_contMDiff (c : Data) (a : ℤ) :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω (restrictionBundleEquiv c a).symm := by
  intro z
  let f := selectedFrame c a z.proj
  have hf : z.proj ∈ restrictionPatch c f := selectedFrame_mem c a z.proj
  let el := (ProjectiveLineBundle.core a).localTriv f.1
  let er := restrictedTriv c a f
  haveI : MemTrivializationAtlas el := ⟨⟨f.1,rfl⟩⟩
  apply (er.contMDiffAt_iff (show (restrictionBundleEquiv c a).symm z ∈ er.source from hf.2)).mpr
  constructor
  · exact Bundle.contMDiffAt_proj (ProjectiveLineBundle.core a).Fiber
  · have hL : ContMDiffAt (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω el z :=
      el.contMDiffOn.contMDiffAt (el.open_source.mem_nhds hf.1)
    apply hL.snd.congr_of_eventuallyEq
    have hU := ((restrictionPatch_isOpen c f).preimage
      (FiberBundle.continuous_proj ℂ (ProjectiveLineBundle.core a).Fiber)).mem_nhds hf
    filter_upwards [hU] with w hw
    exact congrArg Prod.snd (restrictionBundleEquiv_symm_localTriv c a f w hw)

/-- Actual analytic base-preserving fibrewise complex-linear bundle isomorphism
param* core(t,a,0) ≃ O(a). It includes the genuine H restriction at a = 1. -/
def restrictionBundleHomeomorph (c : Data) (a : ℤ) :
    RestrictedTotal c a ≃ₜ (ProjectiveLineBundle.core a).TotalSpace where
  toEquiv := restrictionBundleEquiv c a
  continuous_toFun := (restrictionBundleEquiv_contMDiff c a).continuous
  continuous_invFun := (restrictionBundleEquiv_symm_contMDiff c a).continuous

theorem restrictionBundleHomeomorph_analytic (c : Data) (a : ℤ) :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω (restrictionBundleHomeomorph c a) ∧
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω (restrictionBundleHomeomorph c a).symm :=
  ⟨restrictionBundleEquiv_contMDiff c a,restrictionBundleEquiv_symm_contMDiff c a⟩

/-- In particular the genuine H bundle restricts to the actual analytic O(1). -/
def hyperplaneRestrictionHomeomorph (c : Data) :
    TotalSpace ℂ ((analyticParam c) *ᵖ (FixedFiberBundle.core c.t 1 (fun _ => 0)).Fiber) ≃ₜ
      (ProjectiveLineBundle.core 1).TotalSpace := restrictionBundleHomeomorph c 1

theorem hyperplaneRestrictionHomeomorph_analytic (c : Data) :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω (hyperplaneRestrictionHomeomorph c) ∧
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω (hyperplaneRestrictionHomeomorph c).symm :=
  restrictionBundleHomeomorph_analytic c 1

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.HyperplaneCurve
