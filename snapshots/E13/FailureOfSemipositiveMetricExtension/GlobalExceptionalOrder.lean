import FailureOfSemipositiveMetricExtension.GlobalExceptionalSection
import FailureOfSemipositiveMetricExtension.GlobalExceptional

/-! Simple vanishing of the exceptional sections in genuine global bundle charts. -/
namespace FailureOfSemipositiveMetricExtension.GlobalLineBundle
noncomputable section
open Set Bundle FailureOfSemipositiveMetricExtension.GlobalIncidence
open scoped Manifold ContDiff
attribute [local instance] Classical.propDecidable

theorem exceptionalCoefficient_chartParam (r : Fin 4) (e : Fin 2) (b : Fin 4 → Fin 2)
    (hb : b r = e) (q : ChartCoord) :
    exceptionalCoefficient r (baseChart r,b) (chartParam r e q) = q.1.1 := by
  unfold exceptionalCoefficient
  change pairMap r q.2
    (FailureOfSemipositiveMetricExtension.ProjectivePlane.vector (baseChart r)
      (FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates (baseChart r)
        (affineBase r q.2 (FailureOfSemipositiveMetricExtension.Blowup.projection (localParam e q.1))))) (b r) = _
  rw [affineBase_eq_param,FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates_param]
  have hv : FailureOfSemipositiveMetricExtension.ProjectivePlane.vector (baseChart r)
      (baseCoordinates r q.2 (FailureOfSemipositiveMetricExtension.Blowup.projection (localParam e q.1))) =
      baseVector r q.2 (FailureOfSemipositiveMetricExtension.Blowup.projection (localParam e q.1)) := by
    fin_cases r <;> rfl
  rw [hv,pairMap_baseVector,hb]
  fin_cases e <;> rfl

/-- Every exceptional zero is represented by an actual global chart, with an actual
bundle trivialization, in which the section coefficient is exactly the radial coordinate. -/
theorem exceptionalSection_local_simple_zero (r : Fin 4) (p : Total)
    (hp : sectionValue (exceptionalSection r) p = 0) :
    ∃ (e : Fin 2) (q : ChartCoord) (i : Index),
      p = chartParam r e q ∧ q ∈ chartDomain r e ∧ q.1.1 = 0 ∧ p ∈ baseSet i ∧
      ∀ q' : ChartCoord, exceptionalCoefficient r i (chartParam r e q') = q'.1.1 := by
  have hz := (exceptionalSection_zero_iff r p).mp hp
  obtain ⟨e,s,hs⟩ := FailureOfSemipositiveMetricExtension.ProjectiveLine.charts_cover (directions p r)
  let b0 := ((core 1 (exceptionalDegree r)).indexAt p).2
  let b : Fin 4 → Fin 2 := Function.update b0 r e
  have hb : b r = e := by simp [b]
  have heq : p = pointOverCentre r (projection p) (directions p r) := by
    exact (congrArg Subtype.val
      ((exceptionalFiberEquiv r (projection p)).left_inv ⟨p,hz,rfl⟩)).symm
  have hchart : p = chartParam r e ((0,s),projection p) := by
    rw [chartParam_exceptional,← hs]
    exact heq
  refine ⟨e,((0,s),projection p),(baseChart r,b),hchart,
    exceptional_mem_chartDomain r e s (projection p),rfl,?_,?_⟩
  · constructor
    · rw [hz,← affineBase_zero r (projection p)]
      exact affineBase_mem_chartSet r (projection p) 0
    · intro j
      by_cases hj : j = r
      · subst j
        change directions p r ∈ FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet (b r)
        rw [hb]
        exact ⟨s,hs.symm⟩
      · have hm := ((core 1 (exceptionalDegree r)).mem_baseSet_at p).2 j
        simpa [b,Function.update_of_ne hj] using hm
  · exact exceptionalCoefficient_chartParam r e b hb
end
end FailureOfSemipositiveMetricExtension.GlobalLineBundle
