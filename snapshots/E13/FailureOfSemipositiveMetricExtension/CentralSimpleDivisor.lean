import FailureOfSemipositiveMetricExtension.CentralNormalIdeals
import FailureOfSemipositiveMetricExtension.MultiplierGerms

/-! The actual ell equation is a simple divisor in every actual bundle frame.
This proves the coordinate/unit hypothesis needed by the generic smooth-divisor
multiplier theorem, without taking the paper's ideal formula as an assumption. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold TopologicalSpace
open scoped Manifold ContDiff

def fiberAnalyticCoordinate (t : ℂ) (r : Fin 4) (e : Fin 2) :
    FailureOfSemipositiveMetricExtension.Multiplier.AnalyticCoordinate (Fiber t) where
  chart := FixedFiber.chart t r e
  forward := FixedFiber.coordinates_contMDiffOn t r e ω
  inverse := FixedFiber.param_contMDiffOn t r e ω

def restrictedFiberCoordinate (t : ℂ) (r : Fin 4) (e : Fin 2)
    (U : Set (Fiber t)) (hU : IsOpen U) : FailureOfSemipositiveMetricExtension.Multiplier.AnalyticCoordinate (Fiber t) where
  chart := (FixedFiber.chart t r e).restrOpen U hU
  forward := (FixedFiber.coordinates_contMDiffOn t r e ω).mono (fun _ h => h.1)
  inverse := (FixedFiber.param_contMDiffOn t r e ω).mono (fun _ h => h.1)

theorem ellSection_simple_equation (i : Index) (p : Fiber 0) (hp : p ∈ baseSet 0 i)
    (hz : (coefficientSection ellSection i) ⟨p,hp⟩ = 0) :
    FailureOfSemipositiveMetricExtension.Multiplier.SimpleEquationAt (Fiber 0) (frameOpen 0 i)
      (coefficientSection ellSection i) p := by
  have hv : sectionValue ellSection p = 0 := (sectionValue_zero_iff ellSection i p hp).mpr hz
  obtain ⟨d,hd,hr,he,hform⟩ := ellSection_simple_at_zero p hv
  let U := divisionPatch 0 d ∩ baseSet 0 i
  have hU : IsOpen U := (divisionPatch_isOpen 0 d).inter (baseSet_isOpen 0 i)
  refine ⟨restrictedFiberCoordinate 0 d.1 d.2.1 U hU,⟨hd.1,hd,hp⟩,
    (fun _ h => h.2.2),
    (fun q => gain 0 (-2) ellDegree (divisionFrame d) i q * ellLocalUnit d q),?_,?_,?_⟩
  · have hg := (gain_contMDiffOn 0 (-2) ellDegree (divisionFrame d) i ω).mono
      (t := (restrictedFiberCoordinate 0 d.1 d.2.1 U hU).chart.source)
      (fun q h => ⟨h.2.1.2,h.2.2⟩)
    have hu := (ellLocalUnit_contMDiffOn d).mono
      (t := (restrictedFiberCoordinate 0 d.1 d.2.1 U hU).chart.source) (fun _ h => h.2.1)
    simpa only [smul_eq_mul] using hg.smul hu
  · intro q hq
    exact mul_ne_zero (gain_ne_zero 0 (-2) ellDegree (divisionFrame d) i q ⟨hq.2.1.2,hq.2.2⟩)
      (ellLocalUnit_ne_zero d q hq.2.1)
  · intro q hq
    rw [FailureOfSemipositiveMetricExtension.Multiplier.sectionFunction_of_mem _ _ _ q hq.2.2]
    change ellSection.coefficient i q = (FixedFiber.coordinates 0 d.1 d.2.1 q).2 * _
    rw [← ellSection.compatible (divisionFrame d) i q ⟨hq.2.1.2,hq.2.2⟩,
      ellSection_coefficient_simple d hr he q hq.2.1]
    ring

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
