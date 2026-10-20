import FailureOfSemipositiveMetricExtension.ProjectiveDirectionProduct

/-! Analyticity of the actual incidence inclusion into its original projective
ambient product. The finite direction product retains the original topology. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence
noncomputable section
open Set Topology IsManifold
open scoped Manifold ContDiff

/-- The standard complex seven-dimensional model of the original ambient product. -/
abbrev ambientModel := 𝓘(ℂ,ℂ × ℂ).prod
  (𝓘(ℂ,ProjectiveDirectionProduct.Coord).prod 𝓘(ℂ))

theorem ambient_complex_analytic : IsManifold ambientModel ω Ambient := inferInstance

theorem directions_contMDiff (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ,ChartCoord) 𝓘(ℂ,ProjectiveDirectionProduct.Coord) n directions :=
  ProjectiveDirectionProduct.contMDiff_of_components _ n (fun r => direction_contMDiff r n)

/-- This is the original subtype inclusion, with all seven complex ambient
coordinates bundled into one genuine analytic map. -/
theorem total_inclusion_contMDiff (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ,ChartCoord) ambientModel n (fun p : Total => p.val) :=
  (blowdown_contMDiff n).prodMk ((directions_contMDiff n).prodMk (projection_contMDiff n))

theorem ambient_base_contMDiff (n : WithTop ℕ∞) :
    ContMDiff ambientModel 𝓘(ℂ,ℂ × ℂ) n (fun q : Ambient => q.1) := contMDiff_fst

theorem ambient_parameter_contMDiff (n : WithTop ℕ∞) :
    ContMDiff ambientModel 𝓘(ℂ) n (fun q : Ambient => q.2.2) :=
  contMDiff_snd.comp contMDiff_snd

theorem ambient_direction_contMDiff (r : Fin 4) (n : WithTop ℕ∞) :
    ContMDiff ambientModel 𝓘(ℂ) n (fun q : Ambient => q.2.1 r) :=
  (ProjectiveDirectionProduct.eval_contMDiff r n).comp (contMDiff_fst.comp contMDiff_snd)

/-- Read the blow-up radial coordinate, slope and family parameter directly in
the projective ambient space. Its restriction is the actual chart inverse. -/
def ambientCoordinates (r : Fin 4) (e : Fin 2) (q : Ambient) : ChartCoord :=
  ((radialCoordinate e (localPair (baseChart r) r q),
    ProjectiveLine.coordinates e (q.2.1 r)),q.2.2)

@[simp] theorem ambientCoordinates_inclusion (r : Fin 4) (e : Fin 2) (p : Total) :
    ambientCoordinates r e p.val = explicitCoordinates r e p := rfl

theorem ambientNormalizedVector_contMDiffAt (a : Fin 3) (n : WithTop ℕ∞)
    (q : Ambient) (hb : q.1 ∈ ProjectivePlane.chartSet a) :
    ContMDiffAt ambientModel 𝓘(ℂ,Fin 3 → ℂ) n
      (fun q : Ambient => ProjectivePlane.vector a (ProjectivePlane.coordinates a q.1)) q := by
  have hbase : ContMDiffAt ambientModel 𝓘(ℂ,ℂ × ℂ) n
      (fun q : Ambient => ProjectivePlane.coordinates a q.1) q :=
    ((planeCoordinates_contMDiffOn a n).contMDiffAt
      ((ProjectivePlane.chartSet_isOpen a).mem_nhds hb)).comp q
        (ambient_base_contMDiff n).contMDiffAt
  exact (normalizedVector_contDiff a n).contMDiff.contMDiffAt.comp q hbase

set_option maxHeartbeats 800000 in
theorem ambientLocalPair_contMDiffAt (a : Fin 3) (r : Fin 4) (n : WithTop ℕ∞)
    (q : Ambient) (hb : q.1 ∈ ProjectivePlane.chartSet a) :
    ContMDiffAt ambientModel 𝓘(ℂ,Blowup.Plane) n (localPair a r) q := by
  have hf : ContMDiff 𝓘(ℂ,ℂ × (Fin 3 → ℂ)) 𝓘(ℂ,Blowup.Plane) n
      (fun x : ℂ × (Fin 3 → ℂ) => pairMap r x.1 x.2) := (pairMap_contDiff r n).contMDiff
  have hg : ContMDiffAt ambientModel 𝓘(ℂ,ℂ × (Fin 3 → ℂ)) n
      (fun x : Ambient => (x.2.2,ProjectivePlane.vector a (ProjectivePlane.coordinates a x.1))) q :=
    (ambient_parameter_contMDiff n).contMDiffAt.prodMk_space
      (ambientNormalizedVector_contMDiffAt a n q hb)
  exact hf.contMDiffAt.comp q hg

theorem ambientCoordinates_contMDiffAt (r : Fin 4) (e : Fin 2) (n : WithTop ℕ∞)
    (q : Ambient) (hb : q.1 ∈ ProjectivePlane.chartSet (baseChart r))
    (hd : q.2.1 r ∈ ProjectiveLine.chartSet e) :
    ContMDiffAt ambientModel 𝓘(ℂ,ChartCoord) n (ambientCoordinates r e) q := by
  have hrad : ContMDiffAt ambientModel 𝓘(ℂ) n
      (fun q : Ambient => radialCoordinate e (localPair (baseChart r) r q)) q :=
    (radialCoordinate_contDiff e n).contMDiff.contMDiffAt.comp q
      (ambientLocalPair_contMDiffAt (baseChart r) r n q hb)
  have hslope : ContMDiffAt ambientModel 𝓘(ℂ) n
      (fun q : Ambient => ProjectiveLine.coordinates e (q.2.1 r)) q :=
    ((lineCoordinates_contMDiffOn e n).contMDiffAt
      ((ProjectiveLine.chartSet_isOpen e).mem_nhds hd)).comp q
        (ambient_direction_contMDiff r n).contMDiffAt
  exact (hrad.prodMk_space hslope).prodMk_space (ambient_parameter_contMDiff n).contMDiffAt

/-- The threefold chart inverse is obtained by restricting an analytic ambient
map, without using a global homogeneous representative. -/
theorem ambientCoordinates_chartSource (r : Fin 4) (e : Fin 2) (p : Total)
    (hp : p ∈ chartSource r e) :
    ambientCoordinates r e p.val = chartCoordinates r e p :=
  (chartCoordinates_eq_explicit r e p hp).symm

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence
