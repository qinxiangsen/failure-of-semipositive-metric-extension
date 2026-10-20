import FailureOfSemipositiveMetricExtension.SingularHermitianWeights
import FailureOfSemipositiveMetricExtension.CentralAdjointSection

/-! The prescribed singular Hermitian weight on the actual central L-type bundle.
Its square identity and singular set are proved; positive curvature, minimality and
Lelong numbers are separate future assertions, not assumed here. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold
open scoped Manifold ContDiff

theorem central_degree_relation :
    (fun r => centralADegree r + ellDegree r) = (fun _ : Fin 4 => (2 : ℤ)) := by
  funext r
  fin_cases r <;> decide

theorem central_gain_square (i j : Index) (p : Fiber 0)
    (hp : p ∈ baseSet 0 i ∩ baseSet 0 j) :
    gain 0 (-2) centralADegree i j p * gain 0 (-2) ellDegree i j p =
      (gain 0 (-2) (fun _ => 1) i j p)^2 := by
  rw [← gain_add 0 (-2) (-2) centralADegree ellDegree i j p hp,central_degree_relation]
  rw [pow_two,← gain_add 0 (-2) (-2) (fun _ => 1) (fun _ => 1) i j p hp]
  rfl

theorem central_log_gain_square (i j : Index) (p : Fiber 0)
    (hp : p ∈ baseSet 0 i ∩ baseSet 0 j) :
    Real.log (Complex.normSq (gain 0 (-2) centralADegree i j p)) +
      Real.log (Complex.normSq (gain 0 (-2) ellDegree i j p)) =
      2 * Real.log (Complex.normSq (gain 0 (-2) (fun _ => 1) i j p)) := by
  have h := congrArg (fun z : ℂ => Real.log (Complex.normSq z)) (central_gain_square i j p hp)
  dsimp only at h
  rw [pow_two,Complex.normSq_mul,Complex.normSq_mul,
    Real.log_mul (ne_of_gt (Complex.normSq_pos.mpr (gain_ne_zero 0 (-2) centralADegree i j p hp)))
      (ne_of_gt (Complex.normSq_pos.mpr (gain_ne_zero 0 (-2) ellDegree i j p hp))),
    Real.log_mul (ne_of_gt (Complex.normSq_pos.mpr (gain_ne_zero 0 (-2) (fun _ => 1) i j p hp)))
      (ne_of_gt (Complex.normSq_pos.mpr (gain_ne_zero 0 (-2) (fun _ => 1) i j p hp)))] at h
  linarith

def centralH0RealWeight (i : Index) (p : Fiber 0) : ℝ :=
  (Real.log (sectionNormSum liftedCentralCubics i p) +
    Real.log (Complex.normSq (ellSection.coefficient i p))) / 2

theorem centralH0RealWeight_transition (i j : Index) (p : Fiber 0)
    (hp : p ∈ baseSet 0 i ∩ baseSet 0 j) (hs : ellSection.coefficient i p ≠ 0) :
    centralH0RealWeight j p = centralH0RealWeight i p +
      Real.log (Complex.normSq (gain 0 (-2) (fun _ => 1) i j p)) := by
  unfold centralH0RealWeight
  rw [sectionNormSum_transition liftedCentralCubics i j p hp,
    ← ellSection.compatible i j p hp,Complex.normSq_mul,
    Real.log_mul (ne_of_gt (Complex.normSq_pos.mpr (gain_ne_zero 0 (-2) centralADegree i j p hp)))
      (ne_of_gt (sectionNormSum_positive liftedCentralCubics liftedCentralCubics_basepoint_free i p hp.1)),
    Real.log_mul (ne_of_gt (Complex.normSq_pos.mpr (gain_ne_zero 0 (-2) ellDegree i j p hp)))
      (ne_of_gt (Complex.normSq_pos.mpr hs))]
  have h := central_log_gain_square i j p hp
  linarith

/-- Actual compatible extended weights, equal to minus infinity exactly on ell. -/
def centralH0 : SingularHermitianWeight 0 (-2) (fun _ => 1) where
  weight i p := if ellSection.coefficient i p = 0 then ⊥ else (centralH0RealWeight i p : ℝ)
  compatible i j p hp := by
    have hc := ellSection.compatible i j p hp
    by_cases hs : ellSection.coefficient i p = 0
    · have hj : ellSection.coefficient j p = 0 := by rw [← hc,hs,mul_zero]
      simp [hs,hj]
    · have hj : ellSection.coefficient j p ≠ 0 := by
        rw [← hc]
        exact mul_ne_zero (gain_ne_zero 0 (-2) ellDegree i j p hp) hs
      simp only [hs,hj,if_false]
      simpa using congrArg (fun x : ℝ => (x : WithBot ℝ))
        (centralH0RealWeight_transition i j p hp hs)

theorem centralH0_eq_bot_iff (i : Index) (p : Fiber 0) (hp : p ∈ baseSet 0 i) :
    centralH0.weight i p = ⊥ ↔ sectionValue ellSection p = 0 := by
  rw [sectionValue_zero_iff ellSection i p hp]
  change (if ellSection.coefficient i p = 0 then ⊥ else (centralH0RealWeight i p : WithBot ℝ)) = ⊥ ↔ _
  split_ifs <;> simp_all

/-- Exact square identity of the prescribed extended weights in every actual frame. -/
theorem centralH0_square (i : Index) (p : Fiber 0) :
    centralH0.weight i p + centralH0.weight i p =
      (smoothMetricWeight centralAMetric).weight i p + (divisorWeight ellSection).weight i p := by
  change (if ellSection.coefficient i p = 0 then ⊥ else (centralH0RealWeight i p : WithBot ℝ)) +
    (if ellSection.coefficient i p = 0 then ⊥ else (centralH0RealWeight i p : WithBot ℝ)) =
    ((-Real.log (centralAMetric.coefficient i p) : ℝ) : WithBot ℝ) +
    (if ellSection.coefficient i p = 0 then ⊥ else
      (Real.log (Complex.normSq (ellSection.coefficient i p)) : WithBot ℝ))
  by_cases hs : ellSection.coefficient i p = 0
  · simp [hs]
  · simp only [hs,if_false]
    rw [centralAMetric_formula,Real.log_inv,neg_neg]
    norm_cast
    change centralH0RealWeight i p + centralH0RealWeight i p =
      Real.log (sectionNormSum liftedCentralCubics i p) + Real.log (Complex.normSq (ellSection.coefficient i p))
    unfold centralH0RealWeight
    ring

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
