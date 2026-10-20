import FailureOfSemipositiveMetricExtension.MetricPlurisubharmonicity

/-! The standard local analytic-singularity condition for the actual extended
weights. It is expressed with actual holomorphic functions and a smooth real
remainder, on open subsets of genuine manifold charts. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set IsManifold
open scoped Manifold ContDiff

/-- Local logarithmic ideals plus a smooth remainder. The positive coefficient
uses log of squared moduli, as in the paper; simultaneous zeros have value −∞. -/
def HasAnalyticSingularities {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ}
    (h : SingularHermitianWeight t a b) : Prop :=
  ∀ i r e p, p ∈ weightChartDomain t i r e →
    ∃ (U : Set FixedFiber.Coord), IsOpen U ∧ p ∈ U ∧ U ⊆ weightChartDomain t i r e ∧
      ∃ (n : ℕ) (c : ℝ) (f : Fin n → FixedFiber.Coord → ℂ) (R : FixedFiber.Coord → ℝ),
        0 < c ∧ (∀ k, ContDiffOn ℂ ω (f k) U) ∧ ContDiffOn ℝ ∞ R U ∧
        ∀ q ∈ U, h.weight i (FixedFiber.param t r e q) =
          FailureOfSemipositiveMetricExtension.logSumSquaresWeight c f q + (R q : WithBot ℝ)

/-- The actual prescribed metric has analytic singularities in every actual
bundle frame and coordinate chart, with the explicit four generators ell·A_k. -/
theorem centralH0_analytic_singularities : HasAnalyticSingularities centralH0 := by
  intro i r e p hp
  refine ⟨weightChartDomain 0 i r e,weightChartDomain_isOpen 0 i r e,hp,Subset.rfl,
    4,1/2,(fun k q => ellSection.coefficient i (FixedFiber.param 0 r e q) *
      (liftedCentralCubics k).coefficient i (FixedFiber.param 0 r e q)),(fun _ => 0),by norm_num,?_,
      contDiffOn_const,?_⟩
  · intro k
    exact (coefficient_contDiffOn_chart ellSection i r e).mul
      (coefficient_contDiffOn_chart (liftedCentralCubics k) i r e)
  · intro q hq
    simpa using centralH0_logSumSquares i (FixedFiber.param 0 r e q) hq.2

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
