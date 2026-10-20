import FailureOfSemipositiveMetricExtension.CaoExtensionInterface
import FailureOfSemipositiveMetricExtension.FamilyNeighbourhoods

/-! Actual geometric data for the review-only Cao interface. This supplies no
extension theorem and introduces no axiom. All geometry is proved in the
original total space and central fibre. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.CaoAdapter
noncomputable section
open Set Topology IsManifold
open scoped Manifold ContDiff

abbrev ChartIndex := Fin 4 × Fin 2

def totalAtlas : CaoExtensionInterface.AnalyticAtlas ChartCoord Total ChartIndex where
  chart d := homeomorphChart d.1 d.2
  forward d := chartCoordinates_contMDiffOn d.1 d.2 ω
  inverse d := chartParam_contMDiffOn d.1 d.2 ω
  cover := exists_homeomorphChart_source

def centralAtlas : CaoExtensionInterface.AnalyticAtlas FixedFiber.Coord (Fiber 0) ChartIndex where
  chart d := FixedFiber.chart 0 d.1 d.2
  forward d := FixedFiber.coordinates_contMDiffOn 0 d.1 d.2 ω
  inverse d := FixedFiber.param_contMDiffOn 0 d.1 d.2 ω
  cover := FixedFiber.charts_cover 0

/-- Every generic family field is instantiated by an already proved actual
geometric fact. In particular π is proper, the central range is exact, and the
same last coordinate gives both the parameter and the reduced central slice. -/
def family : CaoExtensionInterface.AdaptedFamily Total (Fiber 0) ChartIndex where
  projection := GlobalIncidence.projection
  projection_analytic := projection_contMDiff ω
  projection_proper := projection_isProperMap
  inclusion := FixedFiber.inclusion 0
  inclusion_analytic := FixedFiber.inclusion_contMDiff 0 ω
  inclusion_closedEmbedding := FixedFiber.inclusion_isClosedEmbedding 0
  central_range := range_fiber_inclusion 0
  totalAtlas := totalAtlas
  centralAtlas := centralAtlas
  central_source _ := rfl
  adapted_parameter d p hp := by
    change projection p = (chartCoordinates d.1 d.2 p).2
    rw [chartCoordinates_eq_explicit d.1 d.2 p hp]
    rfl
  adapted_inclusion d p hp := FixedFiber.global_coordinates_eq 0 d.1 d.2 p hp

@[simp] theorem family_projection : family.projection = projection := rfl
@[simp] theorem family_inclusion : family.inclusion = FixedFiber.inclusion 0 := rfl
@[simp] theorem family_totalChart (d : ChartIndex) :
    family.totalAtlas.chart d = homeomorphChart d.1 d.2 := rfl
@[simp] theorem family_centralChart (d : ChartIndex) :
    family.centralAtlas.chart d = FixedFiber.chart 0 d.1 d.2 := rfl

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.CaoAdapter
