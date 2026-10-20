import FailureOfSemipositiveMetricExtension.PlurisubharmonicScaling

/-! Positive real scaling of the actual all-truncations circular submean definition. -/
namespace FailureOfSemipositiveMetricExtension
noncomputable section
open Set MeasureTheory Filter Topology

theorem lowerTruncation_scale_le_index (c : ℝ) (hc : 0 < c) (M N : ℕ)
    (hNM : (N:ℝ) ≤ c*M) (u : WithBot ℝ) :
    c*lowerTruncation M u ≤ lowerTruncation N (scaleWeight c u) := by
  cases u with
  | bot => simp only [lowerTruncation,WithBot.unbotD_bot,max_self,scaleWeight_bot]; nlinarith
  | coe x =>
    simp only [scaleWeight_coe,lowerTruncation,WithBot.unbotD_coe,mul_max_of_nonneg _ _ hc.le]
    exact max_le_max le_rfl (by nlinarith)

theorem PlurisubharmonicOn.scale_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u : E → WithBot ℝ} {U : Set E} (hu : PlurisubharmonicOn u U) (hU : IsOpen U)
    (c : ℝ) (hc : 0 < c) : PlurisubharmonicOn (fun x => scaleWeight c (u x)) U := by
  have hc0 : 0 < c := hc
  refine ⟨scaleWeight_upperSemicontinuousOn u U hu.1 c hc0,?_⟩
  intro x v r hr hd N
  let M : ℕ := Nat.ceil ((N:ℝ)/c)
  have hNM : (N:ℝ) ≤ c*M := by
    have h := (div_le_iff₀ hc).mp (Nat.le_ceil ((N:ℝ)/c))
    simpa [mul_comm,M] using h
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
  have hi := lowerTruncation_intervalIntegrable (fun θ => u (γ θ)) husc M 0 (2*Real.pi) hab
  have hsi := lowerTruncation_intervalIntegrable (fun θ => scaleWeight c (u (γ θ))) hsc N 0 (2*Real.pi) hab
  have hmono := intervalIntegral.integral_mono_on hab (hi.const_mul c) hsi
    (fun θ _ => lowerTruncation_scale_le_index c hc M N hNM (u (γ θ)))
  rw [intervalIntegral.integral_const_mul] at hmono
  have hs := hu.2 x v r hr hd M
  cases he : u x with
  | bot => simp [he]
  | coe a =>
    have ha : a ≤ (2*Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2*Real.pi), lowerTruncation M (u (γ θ)) :=
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
