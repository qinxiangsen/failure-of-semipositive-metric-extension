import FailureOfSemipositiveMetricExtension.PlurisubharmonicRestriction
import FailureOfSemipositiveMetricExtension.Semicontinuity

/-! Positive tensor powers of genuine psh weights. All circular truncations are
proved integrable before using monotonicity of their ordinary real integrals. -/
namespace FailureOfSemipositiveMetricExtension
noncomputable section
open Set MeasureTheory Filter Topology

/-- Extended positive scalar multiplication, keeping -infinity at -infinity. -/
def scaleWeight (c : ℝ) (u : WithBot ℝ) : WithBot ℝ := u.map (fun x => c*x)

@[simp] theorem scaleWeight_bot (c : ℝ) : scaleWeight c ⊥ = ⊥ := rfl
@[simp] theorem scaleWeight_coe (c x : ℝ) : scaleWeight c (x : WithBot ℝ) = (c*x : ℝ) := rfl

theorem scaleWeight_lt_coe_iff (c a : ℝ) (hc : 0 < c) (u : WithBot ℝ) :
    scaleWeight c u < (a : WithBot ℝ) ↔ u < (a/c : ℝ) := by
  cases u with
  | bot => simp
  | coe x => simp only [scaleWeight_coe,WithBot.coe_lt_coe]; rw [lt_div_iff₀ hc,mul_comm x c]

theorem scaleWeight_upperSemicontinuousOn {X : Type*} [TopologicalSpace X]
    (u : X → WithBot ℝ) (U : Set X) (hu : UpperSemicontinuousOn u U)
    (c : ℝ) (hc : 0 < c) : UpperSemicontinuousOn (fun x => scaleWeight c (u x)) U := by
  intro x hx a ha
  cases a with
  | bot => exact (not_lt_bot ha).elim
  | coe a =>
    have h := hu x hx (a/c) ((scaleWeight_lt_coe_iff c a hc _).mp ha)
    filter_upwards [h] with y hy
    exact (scaleWeight_lt_coe_iff c a hc _).mpr hy

theorem lowerTruncation_lt_iff (N : ℕ) (u : WithBot ℝ) (a : ℝ) :
    lowerTruncation N u < a ↔ -(N:ℝ) < a ∧ u < (a : WithBot ℝ) := by
  cases u with
  | bot => simp [lowerTruncation]
  | coe x => simp [lowerTruncation,max_lt_iff,and_comm]

theorem lowerTruncation_upperSemicontinuous {X : Type*} [TopologicalSpace X]
    (u : X → WithBot ℝ) (hu : UpperSemicontinuous u) (N : ℕ) :
    UpperSemicontinuous (fun x => lowerTruncation N (u x)) := by
  intro x a ha
  obtain ⟨hN,hx⟩ := (lowerTruncation_lt_iff N _ a).mp ha
  filter_upwards [hu x a hx] with y hy
  exact (lowerTruncation_lt_iff N _ a).mpr ⟨hN,hy⟩

theorem lowerTruncation_intervalIntegrable (u : ℝ → WithBot ℝ) (hu : UpperSemicontinuous u)
    (N : ℕ) (a b : ℝ) (hab : a ≤ b) :
    IntervalIntegrable (fun θ => lowerTruncation N (u θ)) volume a b := by
  obtain ⟨C,hC⟩ := usc_withBot_bounded_above (fun x : Icc a b => u x)
    (hu.comp_continuous continuous_subtype_val)
  let K : ℝ := |C| + N + 1
  have hconst : IntegrableOn (fun _ : ℝ => K) (Icc a b) volume :=
    integrableOn_const.mpr (Or.inr (isCompact_Icc.measure_lt_top))
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  apply hconst.mono' ((lowerTruncation_upperSemicontinuous u hu N).measurable.aestronglyMeasurable.restrict)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  have hb := hC ⟨x,hx⟩
  have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  rw [Real.norm_eq_abs,abs_le]
  cases he : u x with
  | bot => simp only [he,lowerTruncation,WithBot.unbotD_bot,max_self]; constructor <;> dsimp [K] <;> linarith [abs_nonneg C]
  | coe v =>
    have hv : v ≤ C := by simpa only [he,WithBot.coe_le_coe] using hb
    simp only [he,lowerTruncation,WithBot.unbotD_coe]
    constructor
    · exact (show -K ≤ -(N:ℝ) by dsimp [K]; linarith [abs_nonneg C]).trans (le_max_right _ _)
    · exact max_le (by dsimp [K]; linarith [le_abs_self C]) (by dsimp [K]; linarith [abs_nonneg C])

theorem lowerTruncation_scale_le (c : ℝ) (hc : 1 ≤ c) (N : ℕ) (u : WithBot ℝ) :
    c * lowerTruncation N u ≤ lowerTruncation N (scaleWeight c u) := by
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  cases u with
  | bot => simp [lowerTruncation]; nlinarith
  | coe x =>
    simp only [scaleWeight_coe,lowerTruncation,WithBot.unbotD_coe,mul_max_of_nonneg _ _ hc0]
    exact max_le_max le_rfl (by nlinarith)

theorem PlurisubharmonicOn.scale_ge_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u : E → WithBot ℝ} {U : Set E} (hu : PlurisubharmonicOn u U) (hU : IsOpen U)
    (c : ℝ) (hc : 1 ≤ c) : PlurisubharmonicOn (fun x => scaleWeight c (u x)) U := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  refine ⟨scaleWeight_upperSemicontinuousOn u U hu.1 c hc0,?_⟩
  intro x v r hr hd N
  let γ : ℝ → E := fun θ => x + complexCircle r θ • v
  have hγ : Continuous γ := by
    apply continuous_const.add
    apply Continuous.smul _ continuous_const
    exact continuous_const.mul (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const))
  have hγU : ∀ θ, γ θ ∈ U := fun θ => hd _ (le_of_eq (norm_complexCircle r θ hr.le))
  have husc : UpperSemicontinuous (fun θ => u (γ θ)) := by
    intro θ a ha
    have h := hu.1 (γ θ) (hγU θ) a ha
    rw [nhdsWithin_eq_nhds.mpr (hU.mem_nhds (hγU θ))] at h
    exact hγ.continuousAt.tendsto.eventually h
  have hsc : UpperSemicontinuous (fun θ => scaleWeight c (u (γ θ))) := by
    simpa only [upperSemicontinuousOn_univ_iff] using
      scaleWeight_upperSemicontinuousOn (fun θ => u (γ θ)) univ
        (by simpa only [upperSemicontinuousOn_univ_iff] using husc) c hc0
  have hab : (0:ℝ) ≤ 2*Real.pi := by positivity
  have hi := lowerTruncation_intervalIntegrable (fun θ => u (γ θ)) husc N 0 (2*Real.pi) hab
  have hsi := lowerTruncation_intervalIntegrable (fun θ => scaleWeight c (u (γ θ))) hsc N 0 (2*Real.pi) hab
  have hmono := intervalIntegral.integral_mono_on hab (hi.const_mul c) hsi
    (fun θ _ => lowerTruncation_scale_le c hc N (u (γ θ)))
  rw [intervalIntegral.integral_const_mul] at hmono
  have hs := hu.2 x v r hr hd N
  cases he : u x with
  | bot => simp [he]
  | coe a =>
    have ha : a ≤ (2*Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2*Real.pi), lowerTruncation N (u (γ θ)) :=
      WithBot.coe_le_coe.mp (by simpa only [he] using hs)
    change scaleWeight c (u x) ≤ _
    rw [he,scaleWeight_coe]
    apply WithBot.coe_le_coe.mpr
    have hp : 0 ≤ (2*Real.pi)⁻¹ := by positivity
    have hm := mul_le_mul_of_nonneg_left hmono hp
    have hh := mul_le_mul_of_nonneg_left ha hc0.le
    dsimp [γ] at hm hh
    nlinarith

end
end FailureOfSemipositiveMetricExtension
