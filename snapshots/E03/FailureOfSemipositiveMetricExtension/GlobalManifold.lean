import FailureOfSemipositiveMetricExtension.GlobalAtlas
import FailureOfSemipositiveMetricExtension.GlobalChartAnalyticMaps

/-! The eight global charts have genuinely complex-analytic transition maps.
This installs the actual analytic manifold structure on the global incidence
space, preserving its independently verified Hausdorff subspace topology. -/

namespace FailureOfSemipositiveMetricExtension.GlobalIncidence
noncomputable section
open Set IsManifold
open scoped Manifold ContDiff

/-- Normalized projective-plane affine coordinates are analytic on their chart. -/
theorem planeCoordinates_contMDiffOn (a : Fin 3) (n : WithTop ℕ∞) :
    ContMDiffOn 𝓘(ℂ,ℂ × ℂ) 𝓘(ℂ,ℂ × ℂ) n
      (ProjectivePlane.coordinates a) (ProjectivePlane.chartSet a) :=
  contMDiffOn_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas ((ProjectivePlane.mem_atlas_iff _).mpr ⟨a,rfl⟩))

/-- Normalized projective-line affine coordinates are analytic on their chart. -/
theorem lineCoordinates_contMDiffOn (e : Fin 2) (n : WithTop ℕ∞) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) n (ProjectiveLine.coordinates e) (ProjectiveLine.chartSet e) :=
  contMDiffOn_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas ((ProjectiveLine.mem_atlas_iff _).mpr ⟨e,rfl⟩))

theorem normalizedVector_contDiff (a : Fin 3) (n : WithTop ℕ∞) :
    ContDiff ℂ n (ProjectivePlane.vector a) := by
  apply contDiff_pi.mpr
  intro k
  fin_cases a <;> fin_cases k <;> dsimp [ProjectivePlane.vector] <;> fun_prop

theorem radialCoordinate_contDiff (e : Fin 2) (n : WithTop ℕ∞) :
    ContDiff ℂ n (radialCoordinate e) := by
  fin_cases e
  · exact contDiff_apply ℂ ℂ 0
  · exact contDiff_apply ℂ ℂ 1

set_option maxHeartbeats 1200000 in
/-- Every one of the sixty-four global chart changes is analytic on its actual overlap. -/
theorem transition_contDiffOn (i j : Fin 4) (e f : Fin 2) (n : WithTop ℕ∞) :
    ContDiffOn ℂ n ((homeomorphChart i e).symm.trans (homeomorphChart j f))
      ((homeomorphChart i e).symm.trans (homeomorphChart j f)).source := by
  let S := ((homeomorphChart i e).symm.trans (homeomorphChart j f)).source
  have hbase : ContDiffOn ℂ n (fun q => ProjectivePlane.coordinates (baseChart j)
      (blowdown (chartParam i e q))) S := by
    apply ContMDiffOn.contDiffOn
    exact (planeCoordinates_contMDiffOn (baseChart j) n).comp
      (chartParam_blowdown_contMDiff i e n).contMDiffOn
      (fun q hq => (mem_chartSource_iff j f _).mp hq.2 |>.1)
  have hvec := (normalizedVector_contDiff (baseChart j) n).comp_contDiffOn hbase
  have hpair : ContDiffOn ℂ n (fun q => basePair j (chartParam i e q)) S :=
    (pairMap_contDiff j n).comp_contDiffOn (contDiff_snd.contDiffOn.prodMk hvec)
  have hrad := (radialCoordinate_contDiff f n).comp_contDiffOn hpair
  have hslope : ContDiffOn ℂ n (fun q => ProjectiveLine.coordinates f
      (directions (chartParam i e q) j)) S := by
    apply ContMDiffOn.contDiffOn
    exact (lineCoordinates_contMDiffOn f n).comp
      ((chartParam_direction_contMDiffOn i e j n).mono inter_subset_left)
      (fun q hq => (mem_chartSource_iff j f _).mp hq.2 |>.2.1)
  have hall : ContDiffOn ℂ n (fun q => explicitCoordinates j f (chartParam i e q)) S :=
    (hrad.prodMk hslope).prodMk contDiff_snd.contDiffOn
  exact hall.congr (transition_apply i j e f)

/-- Compatibility of every pair of members of the installed atlas. -/
theorem atlas_contDiffOn (n : WithTop ℕ∞) (c c' : PartialHomeomorph Total ChartCoord)
    (hc : c ∈ atlas ChartCoord Total) (hc' : c' ∈ atlas ChartCoord Total) :
    ContDiffOn ℂ n (c.symm.trans c') (c.symm.trans c').source := by
  obtain ⟨i,e,rfl⟩ := (mem_atlas_iff c).mp hc
  obtain ⟨j,f,rfl⟩ := (mem_atlas_iff c').mp hc'
  exact transition_contDiffOn i j e f n

/-- The actual global simultaneous-incidence space is a complex analytic threefold. -/
instance instIsManifoldTotal (n : WithTop ℕ∞) : IsManifold 𝓘(ℂ,ChartCoord) n Total := by
  apply isManifold_of_contDiffOn
  intro c c' hc hc'
  simpa using atlas_contDiffOn n c c' hc hc'

theorem complex_analytic_manifold : IsManifold 𝓘(ℂ,ChartCoord) ω Total := inferInstance

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence
