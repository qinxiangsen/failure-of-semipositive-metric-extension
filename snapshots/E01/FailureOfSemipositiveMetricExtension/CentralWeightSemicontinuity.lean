import FailureOfSemipositiveMetricExtension.CentralSingularRegularity
import Mathlib.Topology.Semicontinuous

/-! Upper semicontinuity of the genuine extended singular weights, including
at their minus-infinity locus. This does not assert plurisubharmonicity. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

def extendedHalfLog (x : ℝ) : WithBot ℝ := if x = 0 then ⊥ else ((Real.log x / 2 : ℝ) : WithBot ℝ)

theorem extendedHalfLog_lt_coe (x c : ℝ) (hx : 0 ≤ x) :
    extendedHalfLog x < (c : WithBot ℝ) ↔ x < Real.exp (2*c) := by
  by_cases hz : x = 0
  · simp [extendedHalfLog,hz,Real.exp_pos]
  · have hp : 0 < x := lt_of_le_of_ne hx (Ne.symm hz)
    simp only [extendedHalfLog,hz,if_false,WithBot.coe_lt_coe]
    rw [div_lt_iff₀ (by norm_num : (0:ℝ)<2),mul_comm c 2,Real.log_lt_iff_lt_exp hp]

theorem extendedHalfLog_upperSemicontinuousOn {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (U : Set X) (hf : ContinuousOn f U) (hn : ∀ p ∈ U, 0 ≤ f p) :
    UpperSemicontinuousOn (fun p => extendedHalfLog (f p)) U := by
  intro p hp c hc
  cases c with
  | bot => exact (not_lt_bot hc).elim
  | coe c =>
    have hfc := (extendedHalfLog_lt_coe (f p) c (hn p hp)).mp hc
    have he := (hf p hp).eventually (isOpen_Iio.mem_nhds hfc)
    filter_upwards [he,self_mem_nhdsWithin] with q hq hqU
    exact (extendedHalfLog_lt_coe (f q) c (hn q hqU)).mpr hq

def centralH0Amplitude (i : Index) (p : Fiber 0) : ℝ :=
  sectionNormSum liftedCentralCubics i p * Complex.normSq (ellSection.coefficient i p)

theorem centralH0Amplitude_nonneg (i : Index) (p : Fiber 0) (hp : p ∈ baseSet 0 i) :
    0 ≤ centralH0Amplitude i p :=
  mul_nonneg (sectionNormSum_positive liftedCentralCubics liftedCentralCubics_basepoint_free i p hp).le
    (Complex.normSq_nonneg _)

theorem centralH0Amplitude_continuousOn (i : Index) :
    ContinuousOn (centralH0Amplitude i) (baseSet 0 i) := by
  exact (sectionNormSum_contMDiffOn liftedCentralCubics i).continuousOn.mul
    (Complex.continuous_normSq.comp_continuousOn (ellSection.analytic i).continuousOn)

theorem centralH0_eq_extendedHalfLog (i : Index) (p : Fiber 0) (hp : p ∈ baseSet 0 i) :
    centralH0.weight i p = extendedHalfLog (centralH0Amplitude i p) := by
  have hS := sectionNormSum_positive liftedCentralCubics liftedCentralCubics_basepoint_free i p hp
  by_cases he : ellSection.coefficient i p = 0
  · simp [centralH0,extendedHalfLog,centralH0Amplitude,he]
  · have hE := Complex.normSq_pos.mpr he
    have hn : centralH0Amplitude i p ≠ 0 := ne_of_gt (mul_pos hS hE)
    simp only [centralH0,he,if_false,extendedHalfLog,hn]
    rw [centralH0Amplitude,Real.log_mul (ne_of_gt hS) (ne_of_gt hE)]
    rfl

theorem centralH0_upperSemicontinuousOn (i : Index) :
    UpperSemicontinuousOn (centralH0.weight i) (baseSet 0 i) := by
  have h := extendedHalfLog_upperSemicontinuousOn (centralH0Amplitude i) (baseSet 0 i)
    (centralH0Amplitude_continuousOn i) (centralH0Amplitude_nonneg i)
  intro p hp c hc
  rw [centralH0_eq_extendedHalfLog i p hp] at hc
  filter_upwards [h p hp c hc,self_mem_nhdsWithin] with q hq hqU
  rwa [centralH0_eq_extendedHalfLog i q hqU]

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
