import FailureOfSemipositiveMetricExtension.IndependentCurrentResidualPotential
import FailureOfSemipositiveMetricExtension.FreshDivisorIntegrationCurrent
import FailureOfSemipositiveMetricExtension.FreshFiniteMetricCurrents
import FailureOfSemipositiveMetricExtension.CurrentResidualStandards

namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.FreshCurrentBridge
noncomputable section
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter IsManifold
open scoped Manifold ContDiff Topology
open WeakComplexHessian PshCurvatureCurrentInterface DistributionalCurrent
open NegativeCurveAdapter IndependentCurrentMetricBridge CurrentResidualStandards

variable {h : SingularHermitianWeight 0 (-2) (fun _ => 1)}

theorem RetainedResidual.finite_at (r : RetainedResidual h) (i : Index) (p : Fiber 0)
    (hp : p ∈ baseSet 0 i) (hfin : h.weight i p ≠ ⊥) :
    r.remainder.weight i p ≠ ⊥ := by
  have he := r.square_identity i p hp
  intro hb
  rw [hb,WithBot.bot_add] at he
  cases hx : h.weight i p with
  | bot => exact hfin hx
  | coe x => simp [hx] at he

theorem RetainedResidual.finite_ae (r : RetainedResidual h)
    (T : PositiveCurrent actualCoordinateAtlas) (hrep : Represents actualFrameAtlas T (weight h))
    (a : CurrentIndex) :
    ∀ᵐ z ∂volume.restrict (centralCurrentCoordinate a).chart.target,
      r.remainder.weight a.1 ((centralCurrentCoordinate a).chart.symm z) ≠ ⊥ := by
  filter_upwards [hrep.finite_ae a,
    ae_restrict_mem (centralCurrentCoordinate a).chart.open_target.measurableSet] with z hz hzU
  exact r.finite_at a.1 _ ((centralCurrentCoordinate a).chart.map_target hzU).2 hz

theorem residual_potential_finite_ae (r : RetainedResidual h)
    (T : PositiveCurrent actualCoordinateAtlas) (hrep : Represents actualFrameAtlas T (weight h))
    (a : CurrentIndex) :
    ∀ᵐ z ∂volume.restrict (centralCurrentCoordinate a).chart.target,
      residualRelativePotential r ((centralCurrentCoordinate a).chart.symm z) ≠ ⊥ := by
  filter_upwards [r.finite_ae T hrep a,
    ae_restrict_mem (centralCurrentCoordinate a).chart.open_target.measurableSet] with z hz hzU
  unfold residualRelativePotential
  rw [relativePotential_eq_frame r.remainder centralAMetric a.1 _
    ((centralCurrentCoordinate a).chart.map_target hzU).2]
  cases he : r.remainder.weight a.1 ((centralCurrentCoordinate a).chart.symm z) with
  | bot => exact (hz he).elim
  | coe x =>
    simp only [← WithBot.coe_add,scaleWeight_coe]
    exact WithBot.coe_ne_bot

/-- The SAME smooth A metric as the paper, not an unrelated class representative. -/
def actualASmoothCurrent : PositiveCurrent actualCoordinateAtlas :=
  finitePshCurrent (smoothMetricWeight centralAMetric) centralAMetric_plurisubharmonic
    (fun _ => Filter.Eventually.of_forall (fun _ => by simp [smoothMetricWeight]))

def aRealWeight (a : CurrentIndex) (z : FixedFiber.Coord) : ℝ :=
  -Real.log (centralAMetric.coefficient a.1 ((centralCurrentCoordinate a).chart.symm z))

theorem a_current_coefficient (a : CurrentIndex) (f : FixedFiber.Coord → ℝ)
    (j k : Fin 2) : coefficient (aRealWeight a) j k f = actualASmoothCurrent.coefficient a j k f := by
  rfl

/-- Unit mass normalization is applied to the actual parametrized, reduced ell
and its actual integration trace, not inserted into its definition. -/
theorem ell_trace_lelong_one (p : Fiber 0) (hz : sectionValue ellSection p = 0)
    (a : CurrentIndex) (ha : p ∈ (centralCurrentCoordinate a).chart.source) :
    HasTraceLelongNumber ellIntegrationCurrent a ((centralCurrentCoordinate a).chart p) 1 := by
  apply Literature.reduced_curve_integration_lelong_one (Fiber 0) CurrentIndex Index
    actualCoordinateAtlas (line (-2) ellDegree) divisor ellIntegrationCurrent
    ellIntegrationCurrent_trace p
  · exact (divisor.zero_range p).mpr hz
  · exact ha

/-- The positive residual is the literal difference from THIS original T and
THIS fixed curve-integration current. -/
def residualCurrent (T : PositiveCurrent actualCoordinateAtlas) : Current actualCoordinateAtlas :=
  T.toCurrent.add (ellIntegrationCurrent.toCurrent.smul (-(1/2)))

def actualHalfAClass : DeRhamCurrentClass actualCoordinateAtlas :=
  deRhamClass (actualASmoothCurrent.toCurrent.smul (1/2))

theorem current_residual_calculus (T : PositiveCurrent actualCoordinateAtlas)
    (hh : HasPlurisubharmonicWeights h) (hrep : Represents actualFrameAtlas T (weight h))
    (r : RetainedResidual h) :
    (residualCurrent T).IsPositive ∧
    LocallyIntegrableGlobal actualCoordinateAtlas (residualRelativePotential r) ∧
    deRhamClass (residualCurrent T) = actualHalfAClass ∧
    ∀ a f, IsTest (centralCurrentCoordinate a).chart.target f → ∀ j k,
      T.coefficient a j k f - (1/2:ℂ) * ellIntegrationCurrent.coefficient a j k f =
        (1/2:ℂ) * actualASmoothCurrent.coefficient a j k f +
        coefficient (realRepresentative (fun z => residualRelativePotential r
          ((centralCurrentCoordinate a).chart.symm z))) j k f := by
  have H := Literature.residual_current_local_calculus (Fiber 0) CurrentIndex
    actualCoordinateAtlas T ellIntegrationCurrent actualASmoothCurrent.toCurrent
    (fun a z => h.weight a.1 ((centralCurrentCoordinate a).chart.symm z))
    (fun a z => r.remainder.weight a.1 ((centralCurrentCoordinate a).chart.symm z))
    (fun a z => (divisorWeight ellSection).weight a.1 ((centralCurrentCoordinate a).chart.symm z))
    aRealWeight (residualRelativePotential r) 2 (by norm_num)
    (fun a => hh a.1 a.2.1 a.2.2) (fun a => r.psh a.1 a.2.1 a.2.2)
    hrep.finite_ae (r.finite_ae T hrep) ellDivisorWeight_locallyIntegrable
    ellDivisorWeight_finite_ae
  have hSmooth (a : CurrentIndex) : ContDiffOn ℝ ω (aRealWeight a)
      (centralCurrentCoordinate a).chart.target := by
    have hs := (residualRelativePotential_chart_quasiPsh r a.1 a.2.1 a.2.2).1
    have he : aRealWeight a = fun z => 2 * centralH0SmoothPart a.1
        (FixedFiber.param 0 a.2.1 a.2.2 z) := by
      funext z
      rw [centralH0SmoothPart_eq_metric]
      unfold aRealWeight
      change -Real.log (centralAMetric.coefficient a.1 (FixedFiber.param 0 a.2.1 a.2.2 z)) = _
      ring
    rw [he]
    exact contDiffOn_const.mul hs
  have hSquare (a : CurrentIndex) (z : FixedFiber.Coord)
      (hz : z ∈ (centralCurrentCoordinate a).chart.target) :
      scaleWeight 2 (h.weight a.1 ((centralCurrentCoordinate a).chart.symm z)) =
        r.remainder.weight a.1 ((centralCurrentCoordinate a).chart.symm z) +
        (divisorWeight ellSection).weight a.1 ((centralCurrentCoordinate a).chart.symm z) := by
    rw [← r.square_identity a.1 _ ((centralCurrentCoordinate a).chart.map_target hz).2]
    cases h.weight a.1 ((centralCurrentCoordinate a).chart.symm z) <;>
      simp only [scaleWeight_bot,WithBot.bot_add,scaleWeight_coe,← WithBot.coe_add]
    congr 1
    ring
  have hPotential (a : CurrentIndex) (z : FixedFiber.Coord)
      (hz : z ∈ (centralCurrentCoordinate a).chart.target) :
      scaleWeight (2:ℝ)⁻¹ (r.remainder.weight a.1 ((centralCurrentCoordinate a).chart.symm z)) =
        residualRelativePotential r ((centralCurrentCoordinate a).chart.symm z) +
          (((2:ℝ)⁻¹ * aRealWeight a z : ℝ) : WithBot ℝ) := by
    have he := residualRelativePotential_add_smooth r a.1 _
      ((centralCurrentCoordinate a).chart.map_target hz).2
    rw [centralH0SmoothPart_eq_metric] at he
    have hg : (2:ℝ)⁻¹ * aRealWeight a z =
        -Real.log (centralAMetric.coefficient a.1 ((centralCurrentCoordinate a).chart.symm z))/2 := by
      unfold aRealWeight
      ring
    rw [hg]
    simpa only [one_div] using he.symm
  have out := H hSmooth hrep.coefficient_eq
    (fun a f hf j k => (ellIntegrationCurrent_coefficient_hessian a f hf j k).symm)
    (fun a f _ j k => a_current_coefficient a f j k) hSquare hPotential
  simpa only [residualCurrent,actualHalfAClass,inv_eq_one_div,
    Complex.ofReal_ofNat,neg_div] using out

/-- One finite endpoint preserving the original all-current quantifier and one
h, one retained residual r, one explicit global u, and fixed I_ell and Theta_A.
Pointwise mass-Lelong >=1/2 on ell is stronger than the generic divisorial bound. -/
theorem actual_independent_current_full_residual
    (T : PositiveCurrent actualCoordinateAtlas)
    (hc : deRhamClass T.toCurrent = actualRealChernClass) :
    ∃ h : SingularHermitianWeight 0 (-2) (fun _ => 1),
      HasPlurisubharmonicWeights h ∧ Represents actualFrameAtlas T (weight h) ∧
      ∃ r : RetainedResidual h,
        (residualCurrent T).IsPositive ∧
        deRhamClass (residualCurrent T) = actualHalfAClass ∧
        UpperSemicontinuous (residualRelativePotential r) ∧
        LocallyIntegrableGlobal actualCoordinateAtlas (residualRelativePotential r) ∧
        (∀ a, ∀ᵐ z ∂volume.restrict (centralCurrentCoordinate a).chart.target,
          residualRelativePotential r ((centralCurrentCoordinate a).chart.symm z) ≠ ⊥) ∧
        (∃ C : ℝ, ∀ p, residualRelativePotential r p ≤ (C : WithBot ℝ)) ∧
        (∀ i p, p ∈ baseSet 0 i → sectionValue ellSection p ≠ 0 →
          h.weight i p = centralH0.weight i p + residualRelativePotential r p) ∧
        (∀ i s e,
          ContDiffOn ℝ ω (fun z => centralH0SmoothPart i (FixedFiber.param 0 s e z))
            (weightChartDomain 0 i s e) ∧
          PlurisubharmonicOn (fun z => residualRelativePotential r (FixedFiber.param 0 s e z) +
            (centralH0SmoothPart i (FixedFiber.param 0 s e z) : WithBot ℝ)) (weightChartDomain 0 i s e)) ∧
        (∀ a f, IsTest (centralCurrentCoordinate a).chart.target f → ∀ j k,
          T.coefficient a j k f - (1/2:ℂ) * ellIntegrationCurrent.coefficient a j k f =
            (1/2:ℂ) * actualASmoothCurrent.coefficient a j k f +
            coefficient (realRepresentative (fun z => residualRelativePotential r
              ((centralCurrentCoordinate a).chart.symm z))) j k f) ∧
        (∀ p, sectionValue ellSection p = 0 → ∀ a,
          p ∈ (centralCurrentCoordinate a).chart.source → ∃ v : ℝ,
            HasTraceLelongNumber T a ((centralCurrentCoordinate a).chart p) v ∧ 1/2 ≤ v) := by
  obtain ⟨h,hh,hrep⟩ := actual_current_same_metric T hc
  obtain ⟨r⟩ := retained_residual_exists h hh
  obtain ⟨hp,hi,hc',hformula⟩ := current_residual_calculus T hh hrep r
  refine ⟨h,hh,hrep,r,hp,hc',residualRelativePotential_upperSemicontinuous r,hi,
    residual_potential_finite_ae r T hrep,residualRelativePotential_bounded_above r,
    residualRelativePotential_difference_off_ell r,
    residualRelativePotential_chart_quasiPsh r,hformula,?_⟩
  intro p hz a ha
  exact Literature.positive_current_lelong_monotonicity (Fiber 0) CurrentIndex
    actualCoordinateAtlas T ellIntegrationCurrent (1/2) (by norm_num) hp a
    ((centralCurrentCoordinate a).chart p) ((centralCurrentCoordinate a).chart.map_source ha)
    (ell_trace_lelong_one p hz a ha)
end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.FreshCurrentBridge
