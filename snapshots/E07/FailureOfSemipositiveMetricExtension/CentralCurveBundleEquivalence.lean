import FailureOfSemipositiveMetricExtension.CentralCurveRestriction

/-! The actual two-frame restricted bundle is analytically equivalent to the
previously constructed projective-line O(a+b₃) bundle.  The map preserves the
base, is complex-linear on every fibre, and is analytic in both directions. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

def restrictionFiberEquiv (a : ℤ) (b : Fin 4 → ℤ) (d : Direction) :
    (restrictedCore a b).Fiber d ≃L[ℂ] (FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.core (a+b 3)).Fiber d :=
  ContinuousLinearEquiv.refl ℂ ℂ

def restrictionBundleEquiv (a : ℤ) (b : Fin 4 → ℤ) :
    (restrictedCore a b).TotalSpace ≃ (FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.core (a+b 3)).TotalSpace where
  toFun z := ⟨z.proj,restrictionFiberEquiv a b z.proj z.2⟩
  invFun z := ⟨z.proj,(restrictionFiberEquiv a b z.proj).symm z.2⟩
  left_inv z := by cases z; rfl
  right_inv z := by cases z; rfl

@[simp] theorem restrictionBundleEquiv_projects (a : ℤ) (b : Fin 4 → ℤ)
    (z : (restrictedCore a b).TotalSpace) : (restrictionBundleEquiv a b z).proj = z.proj := rfl
@[simp] theorem restrictionBundleEquiv_symm_projects (a : ℤ) (b : Fin 4 → ℤ)
    (z : (FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.core (a+b 3)).TotalSpace) :
    ((restrictionBundleEquiv a b).symm z).proj = z.proj := rfl

theorem restrictionBundleEquiv_localTriv (a : ℤ) (b : Fin 4 → ℤ) (i : Fin 2)
    (z : (restrictedCore a b).TotalSpace) (hz : z.proj ∈ FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet i) :
    (FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.core (a+b 3)).localTriv i (restrictionBundleEquiv a b z) =
      (restrictedCore a b).localTriv i z := by
  rw [VectorBundleCore.localTriv_apply,VectorBundleCore.localTriv_apply]
  apply Prod.ext
  · rfl
  · exact congrArg (fun T => T z.2)
      (restrictedCore_eq_projectiveLine_cocycle a b ((restrictedCore a b).indexAt z.proj) i z.proj
        ⟨(restrictedCore a b).mem_baseSet_at z.proj,hz⟩).symm

theorem restrictionBundleEquiv_symm_localTriv (a : ℤ) (b : Fin 4 → ℤ) (i : Fin 2)
    (z : (FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.core (a+b 3)).TotalSpace)
    (hz : z.proj ∈ FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet i) :
    (restrictedCore a b).localTriv i ((restrictionBundleEquiv a b).symm z) =
      (FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.core (a+b 3)).localTriv i z := by
  simpa only [Equiv.apply_symm_apply] using
    (restrictionBundleEquiv_localTriv a b i ((restrictionBundleEquiv a b).symm z) hz).symm

theorem restrictionBundleEquiv_contMDiff (a : ℤ) (b : Fin 4 → ℤ) (n : WithTop ℕ∞) :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) n (restrictionBundleEquiv a b) := by
  intro z
  let i := (restrictedCore a b).indexAt z.proj
  let er := (restrictedCore a b).localTriv i
  let eo := (FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.core (a+b 3)).localTriv i
  haveI : MemTrivializationAtlas er := ⟨⟨i,rfl⟩⟩
  haveI : MemTrivializationAtlas eo := ⟨⟨i,rfl⟩⟩
  have hz : z ∈ er.source := (restrictedCore a b).mem_baseSet_at z.proj
  have hez : restrictionBundleEquiv a b z ∈ eo.source := (restrictedCore a b).mem_baseSet_at z.proj
  apply (eo.contMDiffAt_iff hez).mpr
  constructor
  · exact Bundle.contMDiffAt_proj (restrictedCore a b).Fiber
  · have h : ContMDiffAt (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) n er z :=
      er.contMDiffOn.contMDiffAt (er.open_source.mem_nhds hz)
    apply h.snd.congr_of_eventuallyEq
    filter_upwards [er.open_source.mem_nhds hz] with w hw
    exact congrArg Prod.snd (restrictionBundleEquiv_localTriv a b i w hw)

theorem restrictionBundleEquiv_symm_contMDiff (a : ℤ) (b : Fin 4 → ℤ) (n : WithTop ℕ∞) :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) n (restrictionBundleEquiv a b).symm := by
  intro z
  let i := (FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.core (a+b 3)).indexAt z.proj
  let er := (restrictedCore a b).localTriv i
  let eo := (FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.core (a+b 3)).localTriv i
  haveI : MemTrivializationAtlas er := ⟨⟨i,rfl⟩⟩
  haveI : MemTrivializationAtlas eo := ⟨⟨i,rfl⟩⟩
  have hz : z ∈ eo.source := (FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.core (a+b 3)).mem_baseSet_at z.proj
  have hez : (restrictionBundleEquiv a b).symm z ∈ er.source :=
    (FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.core (a+b 3)).mem_baseSet_at z.proj
  apply (er.contMDiffAt_iff hez).mpr
  constructor
  · exact Bundle.contMDiffAt_proj (FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.core (a+b 3)).Fiber
  · have h : ContMDiffAt (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) n eo z :=
      eo.contMDiffOn.contMDiffAt (eo.open_source.mem_nhds hz)
    apply h.snd.congr_of_eventuallyEq
    filter_upwards [eo.open_source.mem_nhds hz] with w hw
    exact congrArg Prod.snd (restrictionBundleEquiv_symm_localTriv a b i w hw)

/-- A genuine base-preserving, fibrewise linear analytic bundle homeomorphism. -/
def restrictionBundleHomeomorph (a : ℤ) (b : Fin 4 → ℤ) :
    (restrictedCore a b).TotalSpace ≃ₜ (FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.core (a+b 3)).TotalSpace where
  toEquiv := restrictionBundleEquiv a b
  continuous_toFun := (restrictionBundleEquiv_contMDiff a b 0).continuous
  continuous_invFun := (restrictionBundleEquiv_symm_contMDiff a b 0).continuous

@[simp] theorem restrictionBundleHomeomorph_mk (a : ℤ) (b : Fin 4 → ℤ) (d : Direction)
    (v : (restrictedCore a b).Fiber d) :
    restrictionBundleHomeomorph a b ⟨d,v⟩ = ⟨d,restrictionFiberEquiv a b d v⟩ := rfl

theorem restrictionBundleHomeomorph_analytic (a : ℤ) (b : Fin 4 → ℤ) :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω (restrictionBundleHomeomorph a b) ∧
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω (restrictionBundleHomeomorph a b).symm :=
  ⟨restrictionBundleEquiv_contMDiff a b ω,restrictionBundleEquiv_symm_contMDiff a b ω⟩

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
