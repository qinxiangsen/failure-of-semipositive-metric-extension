import FailureOfSemipositiveMetricExtension.GeneralAnalyticChartCalculus

/-! The exact canonical density law, including zero times infinity, in every
complex dimension and every genuine line frame. -/
namespace FailureOfSemipositiveMetricExtension.GeneralCao
noncomputable section
open Set MeasureTheory IsManifold
open scoped Manifold ContDiff ENNReal

variable {n : ℕ} {M N : Type} [TopologicalSpace M] [ChartedSpace (Coord (n+1)) M]
    [TopologicalSpace N] [ChartedSpace (Coord n) N]
    [IsManifold 𝓘(ℂ,Coord n) ω N]
    {A B J : Type} (G : Family n M N A B) (L : AnalyticLine n (M := M) J)

namespace CentralAdjointSection
variable (s : CentralAdjointSection n G L) (h : SemipositiveWeight n G L)

def density (e : GeneralMultiplier.AnalyticCoordinate n N) (i : J) (p : N) : ℝ≥0∞ :=
  ENNReal.ofReal (Complex.normSq (s.chartCoefficient G L e i p)) *
    Multiplier.exponentialWeight (h.weight i (G.inclusion p))

theorem gain_ne_zero (i j : J) (p : N)
    (hi : G.inclusion p ∈ L.core.baseSet i) (hj : G.inclusion p ∈ L.core.baseSet j) :
    L.gain i j (G.inclusion p) ≠ 0 := by
  have he := L.core.coordChange_comp i j i (G.inclusion p) ⟨⟨hi,hj⟩,hi⟩ 1
  rw [L.core.coordChange_self i _ hi] at he
  simp only [L.coordChange_eq,mul_one] at he
  intro hz
  rw [hz,mul_zero] at he
  exact zero_ne_one he

theorem density_change (e f : GeneralMultiplier.AnalyticCoordinate n N)
    (i j : J) (p : N) (he : p ∈ e.chart.source)
    (hi : G.inclusion p ∈ L.core.baseSet i) (hj : G.inclusion p ∈ L.core.baseSet j) :
    s.density G L h f j p = ENNReal.ofReal (Complex.normSq (reverseJacobian e f p)) *
      s.density G L h e i p := by
  unfold density
  rw [s.chartCoefficient_change G L e f i j p he hi hj,h.compatible i j _ ⟨hi,hj⟩]
  simpa only [pow_one] using Multiplier.weighted_norm_frame_change 1
    (reverseJacobian e f p) (L.gain i j (G.inclusion p)) (s.chartCoefficient G L e i p)
    (gain_ne_zero G L i j p hi hj) (h.weight i (G.inclusion p))

theorem density_forward_jacobian (e f : GeneralMultiplier.AnalyticCoordinate n N)
    (i j : J) (q : Coord n) (hq : q ∈ e.changeDomain f)
    (hi : G.inclusion (e.chart.symm q) ∈ L.core.baseSet i)
    (hj : G.inclusion (e.chart.symm q) ∈ L.core.baseSet j) :
    ENNReal.ofReal (Complex.normSq (GeneralComplexJacobian.jacobian (e.change f) q)) *
      s.density G L h f j (e.chart.symm q) = s.density G L h e i (e.chart.symm q) := by
  have he := e.chart.map_target hq.1
  have hr := GeneralMultiplier.AnalyticCoordinate.reverseJacobian_eq e f (e.chart.symm q) he hq.2
  rw [s.density_change G L h e f i j _ he hi hj,hr,← mul_assoc]
  change (_ * ENNReal.ofReal (Complex.normSq
      (GeneralComplexJacobian.jacobian (f.change e) (e.change f q)))) * _ = _
  rw [← ENNReal.ofReal_mul (Complex.normSq_nonneg _),← Complex.normSq_mul,
    mul_comm (GeneralComplexJacobian.jacobian (e.change f) q),e.change_jacobian_inverse f hq]
  simp

theorem density_lintegral_change (e f : GeneralMultiplier.AnalyticCoordinate n N)
    (i j : J) (S : Set (Coord n)) (hS : MeasurableSet S)
    (hdom : S ⊆ e.changeDomain f)
    (hi : MapsTo (G.inclusion ∘ e.chart.symm) S (L.core.baseSet i))
    (hj : MapsTo (G.inclusion ∘ e.chart.symm) S (L.core.baseSet j)) :
    (∫⁻ q in e.change f '' S, s.density G L h f j (f.chart.symm q)) =
      ∫⁻ q in S, s.density G L h e i (e.chart.symm q) := by
  rw [GeneralComplexJacobian.lintegral_image_complex_jacobian hS
    (fun q hq => e.change_differentiableAt f (hdom hq)) ((e.change_injOn f).mono hdom)]
  apply setLIntegral_congr_fun hS
  filter_upwards [] with q hq
  change _ * s.density G L h f j (f.chart.symm (f.chart (e.chart.symm q))) = _
  rw [f.chart.left_inv (hdom hq).2]
  exact s.density_forward_jacobian G L h e f i j q (hdom hq) (hi hq) (hj hq)

end CentralAdjointSection
end
end FailureOfSemipositiveMetricExtension.GeneralCao
