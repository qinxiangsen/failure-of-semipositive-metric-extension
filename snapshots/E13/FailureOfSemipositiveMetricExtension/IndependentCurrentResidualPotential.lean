import FailureOfSemipositiveMetricExtension.IndependentCurrentMetricBridge
import FailureOfSemipositiveMetricExtension.PlurisubharmonicPositiveScaling
import FailureOfSemipositiveMetricExtension.CentralMultiplierStalks

/-! The actual residual relative potential is a global quasi-psh representative
of phi_T-phi_0 away from ell, with a proved single upper bound on the compact
surface. Its quasi-psh meaning is given by an explicit smooth addend in every
covering holomorphic chart and the original circular psh definition. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.FreshCurrentBridge
noncomputable section
open Set Filter MeasureTheory IsManifold
open scoped Topology Manifold ContDiff

variable {h : SingularHermitianWeight 0 (-2) (fun _ => 1)}

def residualRelativePotential (r : RetainedResidual h) (p : Fiber 0) : WithBot ℝ :=
  FailureOfSemipositiveMetricExtension.scaleWeight (1/2) (relativePotential r.remainder centralAMetric p)

theorem centralH0SmoothPart_eq_metric (i : Index) (p : Fiber 0) :
    centralH0SmoothPart i p = -Real.log (centralAMetric.coefficient i p)/2 := by
  rw [centralAMetric_formula,Real.log_inv,neg_neg]
  rfl

theorem residualRelativePotential_add_smooth (r : RetainedResidual h)
    (i : Index) (p : Fiber 0) (hp : p ∈ baseSet 0 i) :
    residualRelativePotential r p + (centralH0SmoothPart i p : WithBot ℝ) =
      FailureOfSemipositiveMetricExtension.scaleWeight (1/2) (r.remainder.weight i p) := by
  unfold residualRelativePotential
  rw [relativePotential_eq_frame r.remainder centralAMetric i p hp,centralH0SmoothPart_eq_metric]
  cases he : r.remainder.weight i p with
  | bot => simp
  | coe x =>
    simp only [← WithBot.coe_add,FailureOfSemipositiveMetricExtension.scaleWeight_coe,WithBot.coe_inj]
    ring

theorem residualRelativePotential_upperSemicontinuous (r : RetainedResidual h) :
    UpperSemicontinuous (residualRelativePotential r) := by
  apply upperSemicontinuousOn_univ_iff.mp
  exact FailureOfSemipositiveMetricExtension.scaleWeight_upperSemicontinuousOn _ univ
    (upperSemicontinuousOn_univ_iff.mpr
      (relativePotential_upperSemicontinuous r.remainder centralAMetric r.upperSemicontinuous))
    (1/2) (by norm_num)

/-- This is the standard local quasi-psh condition with an actual real-analytic
smooth correction, on every chart of the full original coordinate/frame cover. -/
theorem residualRelativePotential_chart_quasiPsh (r : RetainedResidual h)
    (i : Index) (s : Fin 4) (e : Fin 2) :
    ContDiffOn ℝ ω (fun z => centralH0SmoothPart i (FixedFiber.param 0 s e z))
      (weightChartDomain 0 i s e) ∧
    FailureOfSemipositiveMetricExtension.PlurisubharmonicOn (fun z => residualRelativePotential r (FixedFiber.param 0 s e z) +
      (centralH0SmoothPart i (FixedFiber.param 0 s e z) : WithBot ℝ)) (weightChartDomain 0 i s e) := by
  constructor
  · have hS : ContDiffOn ℝ ω (fun z => sectionNormSum liftedCentralCubics i (FixedFiber.param 0 s e z))
        (weightChartDomain 0 i s e) := by
      apply ContDiffOn.sum
      intro k _
      exact (FailureOfSemipositiveMetricExtension.normSq_contDiff_real ω).comp_contDiffOn
        ((coefficient_contDiffOn_chart (liftedCentralCubics k) i s e).restrict_scalars ℝ)
    exact (Real.contDiffOn_log.comp hS (fun z hz =>
      (sectionNormSum_positive liftedCentralCubics liftedCentralCubics_basepoint_free i _ hz.2).ne')).div_const 2
  · apply ((r.psh i s e).scale_pos (weightChartDomain_isOpen 0 i s e) (1/2) (by norm_num)).congrOn
    intro z hz
    exact (residualRelativePotential_add_smooth r i _ hz.2).symm

theorem residualRelativePotential_bounded_above (r : RetainedResidual h) :
    ∃ C : ℝ, ∀ p, residualRelativePotential r p ≤ (C : WithBot ℝ) :=
  FailureOfSemipositiveMetricExtension.usc_withBot_bounded_above _ (residualRelativePotential_upperSemicontinuous r)

/-- Away from the genuine divisor, the global representative is exactly the
original difference of weights, including a possible -infinity weight of h. -/
theorem residualRelativePotential_difference_off_ell (r : RetainedResidual h)
    (i : Index) (p : Fiber 0) (hp : p ∈ baseSet 0 i) (hz : sectionValue ellSection p ≠ 0) :
    h.weight i p = centralH0.weight i p + residualRelativePotential r p := by
  have hE : ellSection.coefficient i p ≠ 0 :=
    fun he => hz ((sectionValue_zero_iff ellSection i p hp).mpr he)
  have hs := r.square_identity i p hp
  have hu := residualRelativePotential_add_smooth r i p hp
  have h0 := centralH0_square i p
  simp only [divisorWeight,logarithmicSectionWeight,hE,if_false] at hs h0
  have hf0 : centralH0.weight i p ≠ ⊥ := (centralH0_eq_bot_iff i p hp).not.mpr hz
  cases hx : h.weight i p <;> cases hy : r.remainder.weight i p <;>
    cases hz0 : centralH0.weight i p <;> cases hzU : residualRelativePotential r p <;>
    simp_all only [WithBot.bot_add,WithBot.add_bot,FailureOfSemipositiveMetricExtension.scaleWeight_bot,
      FailureOfSemipositiveMetricExtension.scaleWeight_coe,← WithBot.coe_add,WithBot.coe_inj,
      WithBot.coe_ne_bot,WithBot.bot_ne_coe,smoothMetricWeight]
  all_goals rw [centralH0SmoothPart_eq_metric] at hu; congr 1; linarith

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.FreshCurrentBridge
