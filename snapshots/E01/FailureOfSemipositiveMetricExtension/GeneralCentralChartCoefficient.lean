import FailureOfSemipositiveMetricExtension.GeneralCanonicalNormPatch
import FailureOfSemipositiveMetricExtension.GeneralGermLocalIntegrability

/-! The atlas coefficients in the statement are identified with the actual
alternating-form coefficients, including arbitrary auxiliary germ charts. -/
namespace FailureOfSemipositiveMetricExtension.GeneralCao
noncomputable section
open Set MeasureTheory Topology IsManifold
open scoped Manifold ContDiff ENNReal

variable {n : ℕ} {M N : Type} [TopologicalSpace M] [ChartedSpace (Coord (n+1)) M]
    [TopologicalSpace N] [ChartedSpace (Coord n) N]
    [IsManifold 𝓘(ℂ,Coord n) ω N]
    {A B J : Type} (G : Family n M N A B) (L : AnalyticLine n (M := M) J)

def Family.centralCoordinate (a : A) : GeneralMultiplier.AnalyticCoordinate n N :=
  ⟨G.centralAtlas.chart a,G.centralAtlas.forward a,G.centralAtlas.inverse a⟩

namespace CentralAdjointSection
variable (s : CentralAdjointSection n G L)

theorem chartCoefficient_central (a : A) (i : J) (p : N) (hp : p ∈ centralPatch n G L a i) :
    s.chartCoefficient G L (G.centralCoordinate a) i p = s.coefficient a i p := by
  let e := G.centralCoordinate a
  have hc := e.mdifferentiable.comp_symm_deriv (e.chart.map_source hp.1)
  rw [e.chart.left_inv hp.1] at hc
  have heq : (fun k => mfderiv 𝓘(ℂ,Coord n) 𝓘(ℂ,Coord n) e.chart p
      (mfderiv 𝓘(ℂ,Coord n) 𝓘(ℂ,Coord n) e.chart.symm (e.chart p) (Pi.basisFun ℂ (Fin n) k))) =
        Pi.basisFun ℂ (Fin n) := by
    funext k
    exact congrArg (fun F : Coord n →L[ℂ] Coord n => F (Pi.basisFun ℂ (Fin n) k)) hc
  change (L.core.localTriv i ⟨G.inclusion p,s.form p
    (fun k => mfderiv 𝓘(ℂ,Coord n) 𝓘(ℂ,Coord n) e.chart.symm (e.chart p) (Pi.basisFun ℂ (Fin n) k))⟩).2 = _
  rw [s.represents a i p hp]
  change s.coefficient a i p * coordinateVolume n
    (fun k => mfderiv 𝓘(ℂ,Coord n) 𝓘(ℂ,Coord n) e.chart p
      (mfderiv 𝓘(ℂ,Coord n) 𝓘(ℂ,Coord n) e.chart.symm (e.chart p) (Pi.basisFun ℂ (Fin n) k))) = _
  rw [heq,coordinateVolume_basis,mul_one]

theorem gain_self (i : J) (p : N) (hp : G.inclusion p ∈ L.core.baseSet i) :
    L.gain i i (G.inclusion p) = 1 := by
  simpa only [L.coordChange_eq,mul_one] using L.core.coordChange_self i (G.inclusion p) hp 1

theorem chartCoefficient_from_central (a : A) (e : GeneralMultiplier.AnalyticCoordinate n N)
    (i : J) (p : N) (hp : p ∈ centralPatch n G L a i) (he : p ∈ e.chart.source) :
    s.chartCoefficient G L e i p =
      GeneralComplexJacobian.jacobian (e.change (G.centralCoordinate a)) (e.chart p) * s.coefficient a i p := by
  rw [s.chartCoefficient_change G L (G.centralCoordinate a) e i i p hp.1 hp.2 hp.2,
    gain_self G L i p hp.2,mul_one,s.chartCoefficient_central G L a i p hp,
    GeneralMultiplier.AnalyticCoordinate.reverseJacobian_eq _ _ p hp.1 he]

theorem density_from_central (h : SemipositiveWeight n G L) (a : A)
    (e : GeneralMultiplier.AnalyticCoordinate n N) (i : J) (p : N)
    (hp : p ∈ centralPatch n G L a i) (he : p ∈ e.chart.source) :
    s.density G L h e i p = ENNReal.ofReal
      (Complex.normSq (GeneralComplexJacobian.jacobian (e.change (G.centralCoordinate a)) (e.chart p))) *
      (ENNReal.ofReal (Complex.normSq (s.coefficient a i p)) *
        Multiplier.exponentialWeight (h.weight i (G.inclusion p))) := by
  rw [density,s.chartCoefficient_from_central G L a e i p hp he,
    Complex.normSq_mul,ENNReal.ofReal_mul (Complex.normSq_nonneg _),mul_assoc]

end CentralAdjointSection
end
end FailureOfSemipositiveMetricExtension.GeneralCao
