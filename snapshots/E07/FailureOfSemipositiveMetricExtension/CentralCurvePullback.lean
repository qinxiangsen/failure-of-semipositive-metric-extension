import FailureOfSemipositiveMetricExtension.CentralCurveRestrictedTotal
import Mathlib.Geometry.Manifold.VectorBundle.Pullback

/-! The standard mathlib analytic pullback of the actual central surface line
bundle along the genuine projective-line parametrization. Its identification
with the previously verified restriction core is fibrewise complex linear and
has exact local trivialization formulas. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.CurvePullback
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

def analyticParam : C^ω⟮𝓘(ℂ), Direction; 𝓘(ℂ,FixedFiber.Coord), GlobalIncidence.Fiber 0⟯ :=
  ⟨lineParam,lineParam_contMDiff ω⟩

abbrev PullbackFiber (a : ℤ) (b : Fin 4 → ℤ) := analyticParam *ᵖ (core 0 a b).Fiber
abbrev PullbackTotal (a : ℤ) (b : Fin 4 → ℤ) := TotalSpace ℂ (PullbackFiber a b)

def pullbackTriv (a : ℤ) (b : Fin 4 → ℤ) (i : Fin 2) :
    Trivialization ℂ (π ℂ (PullbackFiber a b)) :=
  ((core 0 a b).localTriv (restrictionFrame i)).pullback analyticParam

instance pullbackTriv_mem_atlas (a : ℤ) (b : Fin 4 → ℤ) (i : Fin 2) :
    MemTrivializationAtlas (pullbackTriv a b i) := by
  haveI : MemTrivializationAtlas ((core 0 a b).localTriv (restrictionFrame i)) :=
    ⟨⟨restrictionFrame i,rfl⟩⟩
  exact ⟨⟨(core 0 a b).localTriv (restrictionFrame i),inferInstance,rfl⟩⟩

@[simp] theorem pullbackTriv_baseSet (a : ℤ) (b : Fin 4 → ℤ) (i : Fin 2) :
    (pullbackTriv a b i).baseSet = ProjectiveLine.chartSet i :=
  restrictionFrame_baseSet i

theorem pullback_analytic (a : ℤ) (b : Fin 4 → ℤ) :
    ContMDiffVectorBundle ω ℂ (PullbackFiber a b) 𝓘(ℂ) := inferInstance

def fiberEquiv (a : ℤ) (b : Fin 4 → ℤ) (d : Direction) :
    PullbackFiber a b d ≃L[ℂ] (restrictedCore a b).Fiber d :=
  (restrictionLiftFiber a b d).symm

def bundleEquiv (a : ℤ) (b : Fin 4 → ℤ) :
    PullbackTotal a b ≃ (restrictedCore a b).TotalSpace where
  toFun z := ⟨z.proj,fiberEquiv a b z.proj z.2⟩
  invFun z := ⟨z.proj,(fiberEquiv a b z.proj).symm z.2⟩
  left_inv z := by cases z; simp
  right_inv z := by cases z; simp

@[simp] theorem bundleEquiv_projects (a : ℤ) (b : Fin 4 → ℤ) (z : PullbackTotal a b) :
    (bundleEquiv a b z).proj = z.proj := rfl

@[simp] theorem bundleEquiv_symm_projects (a : ℤ) (b : Fin 4 → ℤ)
    (z : (restrictedCore a b).TotalSpace) : ((bundleEquiv a b).symm z).proj = z.proj := rfl

/-- The actual standard pullback and restriction core have identical coordinates
in every selected geometric frame, after the fibrewise isomorphism. -/
theorem bundleEquiv_localTriv (a : ℤ) (b : Fin 4 → ℤ) (i : Fin 2) (z : PullbackTotal a b)
    (hz : z.proj ∈ ProjectiveLine.chartSet i) :
    (restrictedCore a b).localTriv i (bundleEquiv a b z) = pullbackTriv a b i z := by
  apply Prod.ext
  · rfl
  · have h := congrArg Prod.snd (restrictionLift_localTriv a b i (bundleEquiv a b z) hz)
    change ((core 0 a b).localTriv (restrictionFrame i)
      ⟨lineParam z.proj,restrictionLiftFiber a b z.proj ((restrictionLiftFiber a b z.proj).symm z.2)⟩).2 =
      ((restrictedCore a b).localTriv i (bundleEquiv a b z)).2 at h
    rw [ContinuousLinearEquiv.apply_symm_apply] at h
    exact h.symm

theorem bundleEquiv_symm_localTriv (a : ℤ) (b : Fin 4 → ℤ) (i : Fin 2)
    (z : (restrictedCore a b).TotalSpace) (hz : z.proj ∈ ProjectiveLine.chartSet i) :
    pullbackTriv a b i ((bundleEquiv a b).symm z) = (restrictedCore a b).localTriv i z := by
  have h := bundleEquiv_localTriv a b i ((bundleEquiv a b).symm z) hz
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.CurvePullback
