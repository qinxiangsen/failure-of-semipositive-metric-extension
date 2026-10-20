import FailureOfSemipositiveMetricExtension.GlobalHomogeneousSections
import FailureOfSemipositiveMetricExtension.GlobalDivisionCover
import FailureOfSemipositiveMetricExtension.PencilSections

/-! The polynomial divided pullbacks now evaluated in the actual global charts. -/
namespace FailureOfSemipositiveMetricExtension.GlobalLineBundle
noncomputable section
open FailureOfSemipositiveMetricExtension.GlobalIncidence
open scoped ContDiff

def pencilLocalCoefficient (r : Fin 4) (e : Fin 2) (k : Fin 2) (q : ChartCoord) : ℂ :=
  match r with
  | 0 => if e = 0 then FailureOfSemipositiveMetricExtension.PencilSections.x₁ q.2 q.1.1 q.1.2 k
    else FailureOfSemipositiveMetricExtension.PencilSections.y₁ q.2 q.1.1 q.1.2 k
  | 1 => if e = 0 then FailureOfSemipositiveMetricExtension.PencilSections.x₂ q.2 q.1.1 q.1.2 k
    else FailureOfSemipositiveMetricExtension.PencilSections.y₂ q.2 q.1.1 q.1.2 k
  | 2 => if e = 0 then FailureOfSemipositiveMetricExtension.PencilSections.x₃ q.2 q.1.1 q.1.2 k
    else FailureOfSemipositiveMetricExtension.PencilSections.y₃ q.2 q.1.1 q.1.2 k
  | 3 => if e = 0 then FailureOfSemipositiveMetricExtension.PencilSections.x₄ q.2 q.1.1 q.1.2 k
    else FailureOfSemipositiveMetricExtension.PencilSections.y₄ q.2 q.1.1 q.1.2 k

theorem pencilLocalCoefficient_contDiff (r : Fin 4) (e : Fin 2) (k : Fin 2) :
    ContDiff ℂ ω (pencilLocalCoefficient r e k) := by
  change ContDiff ℂ ω (fun q => pencilLocalCoefficient r e k q)
  fin_cases r <;> fin_cases e <;> fin_cases k <;>
    dsimp [pencilLocalCoefficient,FailureOfSemipositiveMetricExtension.PencilSections.x₁,FailureOfSemipositiveMetricExtension.PencilSections.y₁,
      FailureOfSemipositiveMetricExtension.PencilSections.x₂,FailureOfSemipositiveMetricExtension.PencilSections.y₂,
      FailureOfSemipositiveMetricExtension.PencilSections.x₃,FailureOfSemipositiveMetricExtension.PencilSections.y₃,
      FailureOfSemipositiveMetricExtension.PencilSections.x₄,FailureOfSemipositiveMetricExtension.PencilSections.y₄] <;> fun_prop

theorem pencil_divided_pullback (r : Fin 4) (e : Fin 2) (k : Fin 2) (q : ChartCoord) :
    (pencilHomogeneous k).value (q.2,baseVector r q.2 (FailureOfSemipositiveMetricExtension.Blowup.projection (localParam e q.1))) =
      q.1.1 * pencilLocalCoefficient r e k q := by
  fin_cases r <;> fin_cases e <;> fin_cases k <;>
    dsimp [pencilHomogeneous,FailureOfSemipositiveMetricExtension.Coordinates.F₁,FailureOfSemipositiveMetricExtension.Coordinates.F₂,
      baseVector,localParam,FailureOfSemipositiveMetricExtension.Blowup.projection,FailureOfSemipositiveMetricExtension.Blowup.X,FailureOfSemipositiveMetricExtension.Blowup.Y,
      pencilLocalCoefficient,FailureOfSemipositiveMetricExtension.PencilSections.x₁,FailureOfSemipositiveMetricExtension.PencilSections.y₁,
      FailureOfSemipositiveMetricExtension.PencilSections.x₂,FailureOfSemipositiveMetricExtension.PencilSections.y₂,
      FailureOfSemipositiveMetricExtension.PencilSections.x₃,FailureOfSemipositiveMetricExtension.PencilSections.y₃,
      FailureOfSemipositiveMetricExtension.PencilSections.x₄,FailureOfSemipositiveMetricExtension.PencilSections.y₄] <;> ring

theorem pulledBackPencil_chartParam (k : Fin 2) (d : DivisionIndex) (q : ChartCoord) :
    (pulledBackPencil k).coefficient (divisionFrame d) (chartParam d.1 d.2.1 q) =
      q.1.1 * pencilLocalCoefficient d.1 d.2.1 k q := by
  change (pencilHomogeneous k).value (q.2,
    FailureOfSemipositiveMetricExtension.ProjectivePlane.vector (baseChart d.1)
      (FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates (baseChart d.1)
        (affineBase d.1 q.2 (FailureOfSemipositiveMetricExtension.Blowup.projection (localParam d.2.1 q.1))))) = _
  rw [affineBase_eq_param,FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates_param]
  have hv : FailureOfSemipositiveMetricExtension.ProjectivePlane.vector (baseChart d.1)
      (baseCoordinates d.1 q.2 (FailureOfSemipositiveMetricExtension.Blowup.projection (localParam d.2.1 q.1))) =
      baseVector d.1 q.2 (FailureOfSemipositiveMetricExtension.Blowup.projection (localParam d.2.1 q.1)) := by
    rcases d with ⟨r,e,b⟩
    fin_cases r <;> rfl
  rw [hv]
  exact pencil_divided_pullback _ _ _ _
end
end FailureOfSemipositiveMetricExtension.GlobalLineBundle
