import FailureOfSemipositiveMetricExtension.GeneralComplexJacobianMeasure
import FailureOfSemipositiveMetricExtension.MetricDensityTransition

/-! Genuine top-form coefficients in arbitrary analytic charts. Their density
law is derived from the actual alternating form and actual line trivializations. -/
namespace FailureOfSemipositiveMetricExtension.GeneralCao
noncomputable section
open Set Topology Bundle IsManifold Manifold
open scoped Manifold ContDiff ENNReal

variable {n : ℕ} {M N : Type} [TopologicalSpace M] [ChartedSpace (Coord (n+1)) M]
    [TopologicalSpace N] [ChartedSpace (Coord n) N]
    [IsManifold 𝓘(ℂ,Coord n) ω N]
    {A B J : Type} (G : Family n M N A B) (L : AnalyticLine n (M := M) J)

namespace CentralAdjointSection
variable (s : CentralAdjointSection n G L)

def scalarForm (i : J) (p : N) : (TangentSpace 𝓘(ℂ,Coord n) p) [⋀^Fin n]→ₗ[ℂ] ℂ :=
  (L.core.coordChange (L.core.indexAt (G.inclusion p)) i (G.inclusion p)).toLinearMap.compAlternatingMap (s.form p)

def chartForm (e : GeneralMultiplier.AnalyticCoordinate n N) (i : J) (p : N) :
    Coord n [⋀^Fin n]→ₗ[ℂ] ℂ :=
  (s.scalarForm G L i p).compLinearMap
    (mfderiv 𝓘(ℂ,Coord n) 𝓘(ℂ,Coord n) e.chart.symm (e.chart p)).toLinearMap

def chartCoefficient (e : GeneralMultiplier.AnalyticCoordinate n N) (i : J) (p : N) : ℂ :=
  s.chartForm G L e i p (Pi.basisFun ℂ (Fin n))

theorem chartForm_eq (e : GeneralMultiplier.AnalyticCoordinate n N) (i : J) (p : N) :
    s.chartForm G L e i p = s.chartCoefficient G L e i p • coordinateVolume n :=
  AlternatingMap.eq_smul_basis_det (Pi.basisFun ℂ (Fin n)) _

theorem chart_represents (e : GeneralMultiplier.AnalyticCoordinate n N) (i : J) (p : N)
    (hp : p ∈ e.chart.source) (v : Fin n → TangentSpace 𝓘(ℂ,Coord n) p) :
    (L.core.localTriv i ⟨G.inclusion p,s.form p v⟩).2 =
      s.chartCoefficient G L e i p * coordinateVolume n
        (fun k => mfderiv 𝓘(ℂ,Coord n) 𝓘(ℂ,Coord n) e.chart p (v k)) := by
  have he : e.chart.MDifferentiable 𝓘(ℂ,Coord n) 𝓘(ℂ,Coord n) :=
    ⟨e.forward.mdifferentiableOn (by simp),e.inverse.mdifferentiableOn (by simp)⟩
  have hc := he.symm_comp_deriv hp
  have h := congrArg (fun f : Coord n [⋀^Fin n]→ₗ[ℂ] ℂ =>
    f (fun k => mfderiv 𝓘(ℂ,Coord n) 𝓘(ℂ,Coord n) e.chart p (v k)))
    (s.chartForm_eq G L e i p)
  change (L.core.localTriv i ⟨G.inclusion p,s.form p
      (fun k => (mfderiv 𝓘(ℂ,Coord n) 𝓘(ℂ,Coord n) e.chart.symm (e.chart p))
        (mfderiv 𝓘(ℂ,Coord n) 𝓘(ℂ,Coord n) e.chart p (v k)))⟩).2 = _ at h
  have heq : (fun k => (mfderiv 𝓘(ℂ,Coord n) 𝓘(ℂ,Coord n) e.chart.symm (e.chart p))
        (mfderiv 𝓘(ℂ,Coord n) 𝓘(ℂ,Coord n) e.chart p (v k))) = v := by
    funext k
    exact congrArg (fun f : TangentSpace 𝓘(ℂ,Coord n) p →L[ℂ] TangentSpace 𝓘(ℂ,Coord n) p => f (v k)) hc
  rwa [heq] at h

def reverseJacobian (e f : GeneralMultiplier.AnalyticCoordinate n N) (p : N) : ℂ :=
  GeneralComplexJacobian.determinant
    ((mfderiv 𝓘(ℂ,Coord n) 𝓘(ℂ,Coord n) e.chart p).comp
      (mfderiv 𝓘(ℂ,Coord n) 𝓘(ℂ,Coord n) f.chart.symm (f.chart p)))

theorem line_frame_change (i j : J) (p : N)
    (hi : G.inclusion p ∈ L.core.baseSet i) (hj : G.inclusion p ∈ L.core.baseSet j)
    (v : L.core.Fiber (G.inclusion p)) :
    (L.core.localTriv j ⟨G.inclusion p,v⟩).2 =
      L.gain i j (G.inclusion p) * (L.core.localTriv i ⟨G.inclusion p,v⟩).2 := by
  simp only [VectorBundleCore.localTriv_apply]
  rw [← L.coordChange_eq]
  exact (L.core.coordChange_comp (L.core.indexAt (G.inclusion p)) i j (G.inclusion p)
    ⟨⟨L.core.mem_baseSet_at _,hi⟩,hj⟩ v).symm

theorem chartCoefficient_change (e f : GeneralMultiplier.AnalyticCoordinate n N)
    (i j : J) (p : N) (he : p ∈ e.chart.source)
    (hi : G.inclusion p ∈ L.core.baseSet i) (hj : G.inclusion p ∈ L.core.baseSet j) :
    s.chartCoefficient G L f j p =
      (reverseJacobian e f p * L.gain i j (G.inclusion p)) * s.chartCoefficient G L e i p := by
  unfold chartCoefficient chartForm scalarForm
  change (L.core.localTriv j ⟨G.inclusion p,s.form p
    (fun k => mfderiv 𝓘(ℂ,Coord n) 𝓘(ℂ,Coord n) f.chart.symm (f.chart p) (Pi.basisFun ℂ (Fin n) k))⟩).2 = _
  rw [line_frame_change G L i j p hi hj,s.chart_represents G L e i p he]
  have hd := congrArg (fun h : Coord n [⋀^Fin n]→ₗ[ℂ] ℂ => h (Pi.basisFun ℂ (Fin n)))
    (GeneralComplexJacobian.coordinateVolume_comp
      ((mfderiv 𝓘(ℂ,Coord n) 𝓘(ℂ,Coord n) e.chart p).comp
        (mfderiv 𝓘(ℂ,Coord n) 𝓘(ℂ,Coord n) f.chart.symm (f.chart p))))
  change coordinateVolume n (fun k => mfderiv 𝓘(ℂ,Coord n) 𝓘(ℂ,Coord n) e.chart p
    (mfderiv 𝓘(ℂ,Coord n) 𝓘(ℂ,Coord n) f.chart.symm (f.chart p) (Pi.basisFun ℂ (Fin n) k))) =
      reverseJacobian e f p * coordinateVolume n (Pi.basisFun ℂ (Fin n)) at hd
  rw [coordinateVolume_basis,mul_one] at hd
  rw [hd]
  dsimp only [chartCoefficient,chartForm,scalarForm]
  ring

end CentralAdjointSection
end
end FailureOfSemipositiveMetricExtension.GeneralCao
