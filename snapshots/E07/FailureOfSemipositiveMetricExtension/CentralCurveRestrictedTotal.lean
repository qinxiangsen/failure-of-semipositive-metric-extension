import FailureOfSemipositiveMetricExtension.CentralCurveRestrictionLift

/-! The genuine restriction of the original surface bundle has its original
subspace topology.  It is homeomorphic to the verified restricted core and hence
to the standard projective-line bundle of degree index a+b₃. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle Topology
open scoped Manifold ContDiff

/-- The original total-space fibres lying over the actual central curve. -/
def RestrictionTotal (a : ℤ) (b : Fin 4 → ℤ) :=
  {z : (core 0 a b).TotalSpace // sectionValue ellSection z.proj = 0}

instance instTopologicalSpaceRestrictionTotal (a : ℤ) (b : Fin 4 → ℤ) :
    TopologicalSpace (RestrictionTotal a b) :=
  inferInstanceAs (TopologicalSpace {z : (core 0 a b).TotalSpace // sectionValue ellSection z.proj = 0})

def restrictionTotalMap (a : ℤ) (b : Fin 4 → ℤ) :
    (restrictedCore a b).TotalSpace → RestrictionTotal a b :=
  fun z => ⟨restrictionLift a b z,ellSection_lineParam_zero z.proj⟩

theorem restrictionTotalMap_bijective (a : ℤ) (b : Fin 4 → ℤ) :
    Function.Bijective (restrictionTotalMap a b) := by
  constructor
  · intro z w h
    exact restrictionLift_injective a b (congrArg Subtype.val h)
  · intro z
    have hz : z.val ∈ Set.range (restrictionLift a b) :=
      (Set.ext_iff.mp (restrictionLift_range a b) z.val).mpr z.property
    obtain ⟨w,hw⟩ := hz
    exact ⟨w,Subtype.ext hw⟩

def restrictionTotalEquiv (a : ℤ) (b : Fin 4 → ℤ) :
    (restrictedCore a b).TotalSpace ≃ RestrictionTotal a b :=
  Equiv.ofBijective (restrictionTotalMap a b) (restrictionTotalMap_bijective a b)

@[simp] theorem restrictionTotalEquiv_apply_val (a : ℤ) (b : Fin 4 → ℤ)
    (z : (restrictedCore a b).TotalSpace) :
    (restrictionTotalEquiv a b z).val = restrictionLift a b z := rfl

@[simp] theorem restrictionTotalEquiv_symm_lift (a : ℤ) (b : Fin 4 → ℤ)
    (z : RestrictionTotal a b) :
    restrictionLift a b ((restrictionTotalEquiv a b).symm z) = z.val :=
  congrArg Subtype.val ((restrictionTotalEquiv a b).apply_symm_apply z)

theorem restrictionTotalEquiv_symm_proj (a : ℤ) (b : Fin 4 → ℤ)
    (z : RestrictionTotal a b) :
    ((restrictionTotalEquiv a b).symm z).proj = directions (FixedFiber.inclusion 0 z.val.proj) 3 := by
  have h := congrArg (fun w : (core 0 a b).TotalSpace =>
    directions (FixedFiber.inclusion 0 w.proj) 3) (restrictionTotalEquiv_symm_lift a b z)
  simpa only [restrictionLift_projects,lineParam_direction_three] using h

theorem restrictionTotalEquiv_symm_continuous (a : ℤ) (b : Fin 4 → ℤ) :
    Continuous (restrictionTotalEquiv a b).symm := by
  have hb : Continuous (fun z : RestrictionTotal a b => ((restrictionTotalEquiv a b).symm z).proj) := by
    simp_rw [restrictionTotalEquiv_symm_proj]
    exact (FixedFiber.direction_contMDiff 0 3 0).continuous.comp
      ((FiberBundle.continuous_proj ℂ (core 0 a b).Fiber).comp continuous_subtype_val)
  apply continuous_iff_continuousAt.mpr
  intro z
  let i := (restrictedCore a b).indexAt ((restrictionTotalEquiv a b).symm z).proj
  let er := (restrictedCore a b).localTriv i
  let ea := (core 0 a b).localTriv (restrictionFrame i)
  have hz : (restrictionTotalEquiv a b).symm z ∈ er.source :=
    (restrictedCore a b).mem_baseSet_at _
  have hsource : (restrictionTotalEquiv a b).symm ⁻¹' er.source ∈ 𝓝 z :=
    ((FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet_isOpen i).preimage hb).mem_nhds hz
  apply (er.toPartialHomeomorph.continuousAt_iff_continuousAt_comp_left hsource).mpr
  have hez : z.val ∈ ea.source := by
    rw [← restrictionTotalEquiv_symm_lift a b z]
    exact (Set.ext_iff.mp (restrictionFrame_baseSet i) _).mpr hz
  have he : ContinuousAt (fun w : RestrictionTotal a b => (ea w.val).2) z :=
    (ea.continuousAt hez).snd.comp continuous_subtype_val.continuousAt
  apply (hb.continuousAt.prodMk he).congr_of_eventuallyEq
  filter_upwards [hsource] with w hw
  have h := restrictionLift_localTriv a b i ((restrictionTotalEquiv a b).symm w) hw
  rw [restrictionTotalEquiv_symm_lift] at h
  apply Prod.ext
  · rfl
  · exact (congrArg Prod.snd h).symm

/-- A homeomorphism to the actual restriction with its inherited topology. -/
def restrictionTotalHomeomorph (a : ℤ) (b : Fin 4 → ℤ) :
    (restrictedCore a b).TotalSpace ≃ₜ RestrictionTotal a b where
  toEquiv := restrictionTotalEquiv a b
  continuous_toFun := (restrictionLift_contMDiff a b 0).continuous.subtype_mk _
  continuous_invFun := restrictionTotalEquiv_symm_continuous a b

/-- The actual subspace restriction is homeomorphic to the standard O(a+b₃) total space. -/
def actualRestrictionHomeomorph (a : ℤ) (b : Fin 4 → ℤ) :
    RestrictionTotal a b ≃ₜ (FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.core (a+b 3)).TotalSpace :=
  (restrictionTotalHomeomorph a b).symm.trans (restrictionBundleHomeomorph a b)

@[simp] theorem actualRestrictionHomeomorph_projects (a : ℤ) (b : Fin 4 → ℤ)
    (z : RestrictionTotal a b) :
    (actualRestrictionHomeomorph a b z).proj = FixedFiber.direction 0 3 z.val.proj :=
  restrictionTotalEquiv_symm_proj a b z

/-- The analytic lift is a closed embedding into the original surface bundle. -/
theorem restrictionLift_isClosedEmbedding (a : ℤ) (b : Fin 4 → ℤ) :
    Topology.IsClosedEmbedding (restrictionLift a b) := by
  have hc : IsClosed {z : (core 0 a b).TotalSpace | sectionValue ellSection z.proj = 0} :=
    ellZeroSet_isClosed.preimage (FiberBundle.continuous_proj ℂ (core 0 a b).Fiber)
  exact hc.isClosedEmbedding_subtypeVal.comp (restrictionTotalHomeomorph a b).isClosedEmbedding

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
