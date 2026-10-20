import FailureOfSemipositiveMetricExtension.CentralTransverseLineAlgebra
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! Actual globally analytic embedded strict transforms of the transverse lines. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.CentralLine
noncomputable section
open Set Topology
open scoped Manifold ContDiff

theorem baseVector_contDiff (c : Data) (n : WithTop ℕ∞) : ContDiff ℂ n (baseVector c) := by
  apply contDiff_pi.mpr
  intro j
  fin_cases j <;> dsimp [baseVector] <;> fun_prop

theorem directionVector_contDiff (c : Data) (r : Fin 4) (n : WithTop ℕ∞) :
    ContDiff ℂ n (directionVector c r) := by
  apply contDiff_pi.mpr
  intro j
  fin_cases r <;> fin_cases j <;> dsimp [directionVector,scaledMap,scale,Blowup.vectorX] <;> fun_prop

theorem base_param (c : Data) (i : Fin 2) (s : ℂ) :
    base c (ProjectiveLine.param i s) =
      ProjectivePlane.vectorPoint (baseVector c (ProjectiveLine.sourceVector i s)) := by
  rw [ProjectiveLine.param_eq_mk_sourceVector,base_mk,ProjectivePlane.vectorPoint_eq_mk _
    (baseVector_ne_zero c _ (ProjectiveLine.sourceVector_ne_zero i s))]

theorem direction_param (c : Data) (r : Fin 4) (i : Fin 2) (s : ℂ) :
    direction c r (ProjectiveLine.param i s) =
      ProjectiveLine.vectorPoint (directionVector c r (ProjectiveLine.sourceVector i s)) := by
  rw [ProjectiveLine.param_eq_mk_sourceVector,direction_mk,ProjectiveLine.vectorPoint_eq_mk _
    (directionVector_ne_zero c r _ (ProjectiveLine.sourceVector_ne_zero i s))]

theorem base_contMDiff (c : Data) (n : WithTop ℕ∞) : ContMDiff 𝓘(ℂ) 𝓘(ℂ,ℂ × ℂ) n (base c) := by
  apply ProjectiveLine.contMDiff_of_param
  intro i
  have heq : (fun s => base c (ProjectiveLine.param i s)) =
      (fun s => ProjectivePlane.vectorPoint (baseVector c (ProjectiveLine.sourceVector i s))) :=
    funext (base_param c i)
  rw [heq]
  intro s
  exact (ProjectivePlane.vectorPoint_contMDiffAt n _
    (baseVector_ne_zero c _ (ProjectiveLine.sourceVector_ne_zero i s))).comp s
      (((baseVector_contDiff c n).comp (ProjectiveLine.sourceVector_contDiff i n)).contMDiff.contMDiffAt)

theorem direction_contMDiff (c : Data) (r : Fin 4) (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) n (direction c r) := by
  apply ProjectiveLine.contMDiff_of_param
  intro i
  have heq : (fun s => direction c r (ProjectiveLine.param i s)) =
      (fun s => ProjectiveLine.vectorPoint (directionVector c r (ProjectiveLine.sourceVector i s))) :=
    funext (direction_param c r i)
  rw [heq]
  intro s
  exact (ProjectiveLine.vectorPoint_contMDiffAt n _
    (directionVector_ne_zero c r _ (ProjectiveLine.sourceVector_ne_zero i s))).comp s
      (((directionVector_contDiff c r n).comp (ProjectiveLine.sourceVector_contDiff i n)).contMDiff.contMDiffAt)

/-- Genuine analyticity into the installed complex surface atlas. -/
theorem param_contMDiff (c : Data) (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) n (param c) :=
  FixedFiber.contMDiff_of_structural_maps 0 𝓘(ℂ) n
    (base_contMDiff c n) (fun r => direction_contMDiff c r n)

theorem param_isClosedEmbedding (c : Data) : Topology.IsClosedEmbedding (param c) :=
  (param_contMDiff c 0).continuous.isClosedEmbedding (param_injective c)

/-- The actual direction-one map provides a left inverse to the actual tangent map. -/
theorem param_mfderiv_leftInverse (c : Data) (d : Direction) :
    ∃ L : TangentSpace 𝓘(ℂ,FixedFiber.Coord) (param c d) →L[ℂ] TangentSpace 𝓘(ℂ) d,
      L.comp (mfderiv 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) (param c) d) =
        ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ) d) := by
  refine ⟨mfderiv 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) (FixedFiber.direction 0 1) (param c d),?_⟩
  have hid : FixedFiber.direction 0 1 ∘ param c = id := funext (param_direction_one c)
  apply ContinuousLinearMap.ext
  intro v
  have hc := mfderiv_comp_apply d
    (((FixedFiber.direction_contMDiff 0 1 1) (param c d)).mdifferentiableAt le_rfl)
    (((param_contMDiff c 1) d).mdifferentiableAt le_rfl) v
  rw [hid,mfderiv_id] at hc
  exact hc.symm

theorem param_mfderiv_injective (c : Data) (d : Direction) :
    Function.Injective (mfderiv 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) (param c) d) := by
  obtain ⟨L,hL⟩ := param_mfderiv_leftInverse c d
  exact (show Function.LeftInverse L (mfderiv 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) (param c) d) from
    fun v => congrArg (fun T => T v) hL).injective

theorem param_closed_holomorphic_embedding (c : Data) :
    IsClosedEmbedding (param c) ∧ ContMDiff 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) ω (param c) ∧
    ∀ d : Direction, Function.Injective (mfderiv 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) (param c) d) :=
  ⟨param_isClosedEmbedding c,param_contMDiff c ω,param_mfderiv_injective c⟩

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.CentralLine
