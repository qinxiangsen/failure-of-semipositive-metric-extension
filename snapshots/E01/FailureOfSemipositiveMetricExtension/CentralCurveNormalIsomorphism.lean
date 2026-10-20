import FailureOfSemipositiveMetricExtension.CentralCurveNormalBundle

/-! The normal line bundle on actual tangent quotients is analytically
isomorphic to the standard pullback of O(ell), hence to the actual P¹ O(-2)
bundle. Both directions use the genuine quotient and pullback topologies. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.CurveNormal
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

def divisorContinuousEquiv (d : Direction) :
    NormalFiber d ≃L[ℂ] CurvePullback.PullbackFiber (-2) ellDegree d := by
  change NormalFiber d ≃L[ℂ] ℂ
  exact frameContinuousEquiv ((core 0 (-2) ellDegree).indexAt (lineParam d)) d
    ((core 0 (-2) ellDegree).mem_baseSet_at (lineParam d))

def divisorBundleEquiv : NormalTotal ≃ CurvePullback.PullbackTotal (-2) ellDegree where
  toFun z := ⟨z.proj,divisorContinuousEquiv z.proj z.2⟩
  invFun z := ⟨z.proj,(divisorContinuousEquiv z.proj).symm z.2⟩
  left_inv z := by cases z; simp
  right_inv z := by cases z; simp

@[simp] theorem divisorBundleEquiv_projects (z : NormalTotal) :
    (divisorBundleEquiv z).proj = z.proj := rfl
@[simp] theorem divisorBundleEquiv_symm_projects (z : CurvePullback.PullbackTotal (-2) ellDegree) :
    (divisorBundleEquiv.symm z).proj = z.proj := rfl

theorem divisorBundleEquiv_localTriv (i : Fin 2) (z : NormalTotal)
    (hz : z.proj ∈ ProjectiveLine.chartSet i) :
    CurvePullback.pullbackTriv (-2) ellDegree i (divisorBundleEquiv z) = localTriv i z := by
  rcases z with ⟨d,v⟩
  rw [localTriv_apply i d hz]
  apply Prod.ext
  · rfl
  · exact divisorFiberEquiv_localTriv (restrictionFrame i) d
      ((Set.ext_iff.mp (restrictionFrame_baseSet i) d).mpr hz) v

theorem divisorBundleEquiv_symm_localTriv (i : Fin 2)
    (z : CurvePullback.PullbackTotal (-2) ellDegree) (hz : z.proj ∈ ProjectiveLine.chartSet i) :
    localTriv i (divisorBundleEquiv.symm z) = CurvePullback.pullbackTriv (-2) ellDegree i z := by
  have h := divisorBundleEquiv_localTriv i (divisorBundleEquiv.symm z) hz
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

theorem divisorBundleEquiv_contMDiff :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω divisorBundleEquiv := by
  intro z
  let i := (restrictedCore (-2) ellDegree).indexAt z.proj
  have hp : z.proj ∈ ProjectiveLine.chartSet i := (restrictedCore (-2) ellDegree).mem_baseSet_at z.proj
  let en := localTriv i
  let ep := CurvePullback.pullbackTriv (-2) ellDegree i
  have hep : divisorBundleEquiv z ∈ ep.source := by
    change z.proj ∈ (CurvePullback.pullbackTriv (-2) ellDegree i).baseSet
    rwa [CurvePullback.pullbackTriv_baseSet]
  apply (ep.contMDiffAt_iff hep).mpr
  constructor
  · exact Bundle.contMDiffAt_proj NormalFiber
  · have hN : ContMDiffAt (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω en z :=
      en.contMDiffOn.contMDiffAt (en.open_source.mem_nhds hp)
    apply hN.snd.congr_of_eventuallyEq
    have hU := ((ProjectiveLine.chartSet_isOpen i).preimage
      (FiberBundle.continuous_proj ℂ NormalFiber)).mem_nhds hp
    filter_upwards [hU] with w hw
    exact congrArg Prod.snd (divisorBundleEquiv_localTriv i w hw)

theorem divisorBundleEquiv_symm_contMDiff :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω divisorBundleEquiv.symm := by
  intro z
  let i := (restrictedCore (-2) ellDegree).indexAt z.proj
  have hp : z.proj ∈ ProjectiveLine.chartSet i := (restrictedCore (-2) ellDegree).mem_baseSet_at z.proj
  let en := localTriv i
  let ep := CurvePullback.pullbackTriv (-2) ellDegree i
  have hep : z ∈ ep.source := by
    change z.proj ∈ (CurvePullback.pullbackTriv (-2) ellDegree i).baseSet
    rwa [CurvePullback.pullbackTriv_baseSet]
  apply (en.contMDiffAt_iff (show divisorBundleEquiv.symm z ∈ en.source from hp)).mpr
  constructor
  · exact Bundle.contMDiffAt_proj (CurvePullback.PullbackFiber (-2) ellDegree)
  · have hP : ContMDiffAt (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω ep z :=
      ep.contMDiffOn.contMDiffAt (ep.open_source.mem_nhds hep)
    apply hP.snd.congr_of_eventuallyEq
    have hU := ((ProjectiveLine.chartSet_isOpen i).preimage
      (FiberBundle.continuous_proj ℂ (CurvePullback.PullbackFiber (-2) ellDegree))).mem_nhds hp
    filter_upwards [hU] with w hw
    exact congrArg Prod.snd (divisorBundleEquiv_symm_localTriv i w hw)

/-- N_lineParam ≃ lineParam*O(ell), via the actual derivative of ellSection. -/
def divisorBundleHomeomorph : NormalTotal ≃ₜ CurvePullback.PullbackTotal (-2) ellDegree where
  toEquiv := divisorBundleEquiv
  continuous_toFun := divisorBundleEquiv_contMDiff.continuous
  continuous_invFun := divisorBundleEquiv_symm_contMDiff.continuous

def degreeFiberEquiv (d : Direction) : NormalFiber d ≃L[ℂ] (ProjectiveLineBundle.core (-2)).Fiber d :=
  (divisorContinuousEquiv d).trans (CurvePullback.ellFiberEquiv d)

/-- The actual quotient normal bundle of the embedded central projective line
is genuinely analytically isomorphic to O(-2). -/
def degreeHomeomorph : NormalTotal ≃ₜ (ProjectiveLineBundle.core (-2)).TotalSpace :=
  divisorBundleHomeomorph.trans CurvePullback.ellHomeomorph

@[simp] theorem degreeHomeomorph_mk (d : Direction) (v : NormalFiber d) :
    degreeHomeomorph ⟨d,v⟩ = ⟨d,degreeFiberEquiv d v⟩ := rfl

@[simp] theorem degreeHomeomorph_projects (z : NormalTotal) : (degreeHomeomorph z).proj = z.proj := rfl

@[simp] theorem degreeHomeomorph_symm_projects (z : (ProjectiveLineBundle.core (-2)).TotalSpace) :
    (degreeHomeomorph.symm z).proj = z.proj := rfl

theorem degreeHomeomorph_contMDiff :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω degreeHomeomorph :=
  CurvePullback.ellHomeomorph_analytic.1.comp divisorBundleEquiv_contMDiff

theorem degreeHomeomorph_symm_contMDiff :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω degreeHomeomorph.symm :=
  divisorBundleEquiv_symm_contMDiff.comp CurvePullback.ellHomeomorph_analytic.2

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.CurveNormal
