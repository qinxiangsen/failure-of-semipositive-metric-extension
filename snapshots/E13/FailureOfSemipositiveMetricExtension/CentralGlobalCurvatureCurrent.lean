import FailureOfSemipositiveMetricExtension.AtlasCurvatureCurrent
import FailureOfSemipositiveMetricExtension.CentralCurvatureLelong
import FailureOfSemipositiveMetricExtension.CentralSimpleDivisor
import FailureOfSemipositiveMetricExtension.Literature.CurrentCovariance

/-! The actual h0 coordinate current is globally compatible on the complete
coordinate/frame cover. Every analytic coordinate and gauge hypothesis is
proved for the real central fibre and its genuine line bundle. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set IsManifold
open scoped Topology Manifold ContDiff
open AtlasCurvature PshCurvatureCurrentInterface

abbrev CurrentIndex := Index × (Fin 4 × Fin 2)

def centralCurrentCoordinate (a : CurrentIndex) : Multiplier.AnalyticCoordinate (Fiber 0) :=
  restrictedFiberCoordinate 0 a.2.1 a.2.2 (baseSet 0 a.1) (baseSet_isOpen 0 a.1)

@[simp] theorem centralCurrentCoordinate_source (a : CurrentIndex) :
    (centralCurrentCoordinate a).chart.source = FixedFiber.source 0 a.2.1 a.2.2 ∩ baseSet 0 a.1 := rfl

@[simp] theorem centralCurrentCoordinate_target (a : CurrentIndex) :
    (centralCurrentCoordinate a).chart.target = weightChartDomain 0 a.1 a.2.1 a.2.2 := rfl

def centralMetricAtlas : AtlasCurvature.MetricAtlas (Fiber 0) CurrentIndex where
  coordinate := centralCurrentCoordinate
  cover p := by
    obtain ⟨⟨r,e⟩,hp⟩ := FixedFiber.charts_cover 0 p
    exact ⟨⟨(core 0 (-2) (fun _ => 1)).indexAt p,⟨r,e⟩⟩,hp,(core 0 (-2) (fun _ => 1)).mem_baseSet_at p⟩
  weight a := centralH0.weight a.1
  gauge a b := gain 0 (-2) (fun _ => 1) b.1 a.1
  gauge_analytic a b := (gain_contMDiffOn 0 (-2) (fun _ => 1) b.1 a.1 ω).mono
    (fun _ h => ⟨h.2.2,h.1.2⟩)
  gauge_nonzero a b p hp := gain_ne_zero 0 (-2) (fun _ => 1) b.1 a.1 p ⟨hp.2.2,hp.1.2⟩
  compatible a b p hp := centralH0.compatible b.1 a.1 p ⟨hp.2.2,hp.1.2⟩
  psh a := centralH0_plurisubharmonic a.1 a.2.1 a.2.2
  finite_dense a := centralH0_finitePointsDense a.1 a.2.1 a.2.2

/-- One globally compatible positive closed coordinate current, with actual
trace-mass Lelong limits in all charts of the genuine covering atlas. -/
theorem centralH0_globalCoordinateCurrent_exists :
    ∃ T : AtlasCurvature.MetricAtlas.GlobalPositiveClosedCurrent centralMetricAtlas,
      ∀ a z, z ∈ (centralCurrentCoordinate a).chart.target →
        HasLelongNumber (T.localCurrent a) z
          (FailureOfSemipositiveMetricExtension.logarithmicOrder (centralMetricAtlas.localWeight a) z) :=
  centralMetricAtlas.globalCurrent_with_lelong_exists
    Literature.psh_curvature_current_lelong_via_distribution_translation
    Literature.distributional_ddc_coordinate_gauge_covariance

def centralH0_globalCoordinateCurrent :
    AtlasCurvature.MetricAtlas.GlobalPositiveClosedCurrent centralMetricAtlas :=
  Classical.choose centralH0_globalCoordinateCurrent_exists

/-- The local mass-defined Lelong numbers now belong to ONE globally
coordinate-compatible current, rather than independently chosen local currents. -/
theorem centralH0_global_current_lelong_half (p : Fiber 0) (hz : sectionValue ellSection p = 0) :
    ∃ a : CurrentIndex, p ∈ (centralCurrentCoordinate a).chart.source ∧
      HasLelongNumber (centralH0_globalCoordinateCurrent.localCurrent a)
        ((centralCurrentCoordinate a).chart p) (1/2) := by
  obtain ⟨d,hp,ho⟩ := centralH0_logarithmic_order p hz
  let a : CurrentIndex := ⟨divisionFrame d,d.1,d.2.1⟩
  have ha : p ∈ (centralCurrentCoordinate a).chart.source := hp
  refine ⟨a,ha,?_⟩
  have h := (Classical.choose_spec centralH0_globalCoordinateCurrent_exists) a
    ((centralCurrentCoordinate a).chart p) ((centralCurrentCoordinate a).chart.map_source ha)
  exact ho ▸ h

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
