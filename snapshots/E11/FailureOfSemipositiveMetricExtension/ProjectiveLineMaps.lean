import FailureOfSemipositiveMetricExtension.ProjectiveLine
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-!
The canonical projective direction of a nonzero complex two-vector is analytic
for the genuine affine-atlas manifold structure on the projective line.
No continuity of a chosen homogeneous representative is used.
-/

noncomputable section

namespace FailureOfSemipositiveMetricExtension.ProjectiveLine

open Set Topology IsManifold
open scoped Manifold ContDiff

/-- The direction of a vector, extended by `[1:0]` at zero. -/
def vectorPoint (v : Blowup.Plane) : Point :=
  if h : v = 0 then param 0 0 else Projectivization.mk ℂ v h

@[simp] theorem vectorPoint_zero : vectorPoint 0 = param 0 0 := by
  simp [vectorPoint]

/-- Away from zero this is precisely the projectivization quotient map. -/
theorem vectorPoint_eq_mk (v : Blowup.Plane) (hv : v ≠ 0) :
    vectorPoint v = Projectivization.mk ℂ v hv := by
  simp [vectorPoint,hv]

/-- Normalize by the first nonzero coordinate. -/
theorem vectorPoint_eq_param_zero (v : Blowup.Plane) (hv : v 0 ≠ 0) :
    vectorPoint v = param 0 (v 1 / v 0) := by
  have hv' : v ≠ 0 := by
    intro h
    exact hv (congrFun h 0)
  rw [vectorPoint_eq_mk v hv',param_zero]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨v 0,?_⟩
  ext i
  fin_cases i <;> simp [Blowup.vectorX,mul_div_cancel₀,hv]

/-- Normalize by the second nonzero coordinate. -/
theorem vectorPoint_eq_param_one (v : Blowup.Plane) (hv : v 1 ≠ 0) :
    vectorPoint v = param 1 (v 0 / v 1) := by
  have hv' : v ≠ 0 := by
    intro h
    exact hv (congrFun h 1)
  rw [vectorPoint_eq_mk v hv',param_one]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨v 1,?_⟩
  ext i
  fin_cases i <;> simp [Blowup.vectorY,mul_div_cancel₀,hv]

/-- Affine parametrizations are analytic into the actual projective line. -/
theorem param_contMDiff (i : Fin 2) (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) n (param i) := by
  have he : homeomorphChart i ∈ maximalAtlas 𝓘(ℂ) n Point :=
    IsManifold.subset_maximalAtlas ((mem_atlas_iff _).mpr ⟨i,rfl⟩)
  exact contMDiffOn_univ.mp (contMDiffOn_symm_of_mem_maximalAtlas he)

/-- The quotient direction is analytic at every nonzero vector. -/
theorem vectorPoint_contMDiffAt (n : WithTop ℕ∞) (v : Blowup.Plane) (hv : v ≠ 0) :
    ContMDiffAt 𝓘(ℂ,Blowup.Plane) 𝓘(ℂ) n vectorPoint v := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      ext i
      fin_cases i <;> simp [h0,h1]
    have hrat : ContDiffAt ℂ n (fun w : Blowup.Plane => w 0 / w 1) v :=
      (contDiff_apply ℂ ℂ 0).contDiffAt.div (contDiff_apply ℂ ℂ 1).contDiffAt h1
    have hlocal := (param_contMDiff 1 n).contMDiffAt.comp v hrat.contMDiffAt
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [(continuous_apply 1).continuousAt.eventually_ne h1] with w hw
    exact vectorPoint_eq_param_one w hw
  · have hrat : ContDiffAt ℂ n (fun w : Blowup.Plane => w 1 / w 0) v :=
      (contDiff_apply ℂ ℂ 1).contDiffAt.div (contDiff_apply ℂ ℂ 0).contDiffAt h0
    have hlocal := (param_contMDiff 0 n).contMDiffAt.comp v hrat.contMDiffAt
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [(continuous_apply 0).continuousAt.eventually_ne h0] with w hw
    exact vectorPoint_eq_param_zero w hw

/-- Analyticity on the full punctured vector space. -/
theorem vectorPoint_contMDiffOn (n : WithTop ℕ∞) :
    ContMDiffOn 𝓘(ℂ,Blowup.Plane) 𝓘(ℂ) n vectorPoint {v | v ≠ 0} := by
  intro v hv
  exact (vectorPoint_contMDiffAt n v hv).contMDiffWithinAt

/-- Continuity of projectivization at each nonzero vector. -/
theorem vectorPoint_continuousAt (v : Blowup.Plane) (hv : v ≠ 0) :
    ContinuousAt vectorPoint v :=
  (vectorPoint_contMDiffAt 0 v hv).continuousAt

/-- The quotient direction is continuous on the punctured vector space. -/
theorem vectorPoint_continuousOn : ContinuousOn vectorPoint {v | v ≠ 0} :=
  (vectorPoint_contMDiffOn 0).continuousOn

/-- A continuous family of nonzero vectors has continuous projective directions. -/
theorem vectorPoint_comp_continuousOn {T : Type*} [TopologicalSpace T]
    {v : T → Blowup.Plane} {s : Set T} (hv : ContinuousOn v s)
    (hne : ∀ t ∈ s, v t ≠ 0) : ContinuousOn (fun t => vectorPoint (v t)) s :=
  vectorPoint_continuousOn.comp hv hne

/-- A nowhere-zero continuous vector family induces a continuous projective map. -/
theorem vectorPoint_comp_continuous {T : Type*} [TopologicalSpace T]
    {v : T → Blowup.Plane} (hv : Continuous v) (hne : ∀ t, v t ≠ 0) :
    Continuous (fun t => vectorPoint (v t)) := by
  exact continuous_iff_continuousOn_univ.mpr
    (vectorPoint_comp_continuousOn hv.continuousOn (fun t _ => hne t))

end FailureOfSemipositiveMetricExtension.ProjectiveLine
