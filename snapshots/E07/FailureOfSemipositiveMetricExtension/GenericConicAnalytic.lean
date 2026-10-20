import FailureOfSemipositiveMetricExtension.GenericConicIncidence
import FailureOfSemipositiveMetricExtension.ProjectivePlaneMaps
import FailureOfSemipositiveMetricExtension.FixedFiberStructuralMaps

/-! The actual conic parametrization is complex analytic on all of P1, including
every exceptional intersection. Its proof uses local normalized vectors only. -/
namespace FailureOfSemipositiveMetricExtension.ProjectiveLine
noncomputable section
open Set Topology
open scoped Manifold ContDiff

def sourceVector (i : Fin 2) (s : ℂ) : Blowup.Plane :=
  if i = 0 then Blowup.vectorX s else Blowup.vectorY s

theorem sourceVector_ne_zero (i : Fin 2) (s : ℂ) : sourceVector i s ≠ 0 := by
  fin_cases i
  · exact Blowup.vectorX_ne_zero s
  · exact Blowup.vectorY_ne_zero s

theorem sourceVector_contDiff (i : Fin 2) (n : WithTop ℕ∞) : ContDiff ℂ n (sourceVector i) := by
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> dsimp [sourceVector,Blowup.vectorX,Blowup.vectorY] <;> fun_prop

theorem param_eq_mk_sourceVector (i : Fin 2) (s : ℂ) :
    param i s = Projectivization.mk ℂ (sourceVector i s) (sourceVector_ne_zero i s) := by
  fin_cases i <;> rfl

/-- Check a map out of the actual projective line in its two actual standard charts. -/
theorem contMDiff_of_param {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℂ E H) (n : WithTop ℕ∞) {g : Point → M}
    (hg : ∀ i, ContMDiff 𝓘(ℂ) I n (fun s => g (param i s))) : ContMDiff 𝓘(ℂ) I n g := by
  intro d
  obtain ⟨i,s,hs⟩ := charts_cover d
  have hd : d ∈ chartSet i := ⟨s,hs.symm⟩
  have hc := (ProjectiveLineBundle.coordinates_contMDiffOn i n).contMDiffAt
    ((chartSet_isOpen i).mem_nhds hd)
  apply ((hg i).contMDiffAt.comp d hc).congr_of_eventuallyEq
  filter_upwards [(chartSet_isOpen i).mem_nhds hd] with w hw
  exact congrArg g (param_coordinates i w hw).symm

end
end FailureOfSemipositiveMetricExtension.ProjectiveLine

namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil.Conic
noncomputable section
open Set Topology
open scoped Manifold ContDiff

theorem baseVector_contDiff (c : Data) (n : WithTop ℕ∞) : ContDiff ℂ n (baseVector c) := by
  apply contDiff_pi.mpr
  intro j
  fin_cases j <;> dsimp [baseVector,denominator] <;> fun_prop

theorem directionMap_contDiff (c : Data) (r : Fin 4) (n : WithTop ℕ∞) :
    ContDiff ℂ n (directionMap c r) := by
  apply contDiff_pi.mpr
  intro j
  fin_cases r <;> fin_cases j <;> dsimp [directionMap,denominator] <;> fun_prop

theorem base_param (c : Data) (i : Fin 2) (s : ℂ) :
    base c (ProjectiveLine.param i s) =
      ProjectivePlane.vectorPoint (baseVector c (ProjectiveLine.sourceVector i s)) := by
  rw [ProjectiveLine.param_eq_mk_sourceVector,base_mk,ProjectivePlane.vectorPoint_eq_mk _
    (baseVector_ne_zero c _ (ProjectiveLine.sourceVector_ne_zero i s))]

theorem direction_param (c : Data) (r : Fin 4) (i : Fin 2) (s : ℂ) :
    direction c r (ProjectiveLine.param i s) =
      ProjectiveLine.vectorPoint (directionMap c r (ProjectiveLine.sourceVector i s)) := by
  rw [ProjectiveLine.param_eq_mk_sourceVector,direction_mk,ProjectiveLine.vectorPoint_eq_mk _
    (directionMap_ne_zero c r _ (ProjectiveLine.sourceVector_ne_zero i s))]

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
      (fun s => ProjectiveLine.vectorPoint (directionMap c r (ProjectiveLine.sourceVector i s))) :=
    funext (direction_param c r i)
  rw [heq]
  intro s
  exact (ProjectiveLine.vectorPoint_contMDiffAt n _
    (directionMap_ne_zero c r _ (ProjectiveLine.sourceVector_ne_zero i s))).comp s
      (((directionMap_contDiff c r n).comp (ProjectiveLine.sourceVector_contDiff i n)).contMDiff.contMDiffAt)

/-- Genuine analyticity into the installed complex surface atlas. -/
theorem param_contMDiff (c : Data) (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) n (param c) :=
  FixedFiber.contMDiff_of_structural_maps c.t 𝓘(ℂ) n
    (base_contMDiff c n) (fun r => direction_contMDiff c r n)

theorem param_isClosedEmbedding (c : Data) : Topology.IsClosedEmbedding (param c) :=
  (param_contMDiff c 0).continuous.isClosedEmbedding (param_injective c)

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil.Conic
