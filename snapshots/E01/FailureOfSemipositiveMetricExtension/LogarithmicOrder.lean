import FailureOfSemipositiveMetricExtension.Plurisubharmonic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The actual logarithmic-growth order of an extended weight, with the paper's
log(norm^2) normalization. This is the growth-side quantity in the standard
Lelong characterization (Demailly Theorem 2.8(b)); no current is postulated here. -/
namespace FailureOfSemipositiveMetricExtension
noncomputable section
open Set Filter
open scoped Topology

abbrev SurfaceCoord := ℂ × ℂ

def LogarithmicUpperBound (u : SurfaceCoord → WithBot ℝ) (p : SurfaceCoord) (c : ℝ) : Prop :=
  ∃ (C r : ℝ), 0 < r ∧ ∀ z, dist z p < r → z ≠ p →
    u z ≤ ((c * Real.log (‖z-p‖^2) + C : ℝ) : WithBot ℝ)

def logarithmicOrder (u : SurfaceCoord → WithBot ℝ) (p : SurfaceCoord) : ℝ :=
  sSup {c : ℝ | 0 ≤ c ∧ LogarithmicUpperBound u p c}

def normalLogWeight (a : ℝ) (R : SurfaceCoord → ℝ) (z : SurfaceCoord) : WithBot ℝ :=
  if z.2 = 0 then ⊥ else ((a * Real.log (Complex.normSq z.2) + R z : ℝ) : WithBot ℝ)

theorem LogarithmicUpperBound.congr_nhds {u v : SurfaceCoord → WithBot ℝ}
    {p : SurfaceCoord} {c : ℝ} (h : LogarithmicUpperBound u p c)
    (he : u =ᶠ[𝓝 p] v) : LogarithmicUpperBound v p c := by
  obtain ⟨C,r,hr,hb⟩ := h
  obtain ⟨δ,hδ,hδe⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨C,min r δ,lt_min hr hδ,?_⟩
  intro z hz hzp
  rw [← hδe (lt_of_lt_of_le hz (min_le_right _ _))]
  exact hb z (lt_of_lt_of_le hz (min_le_left _ _)) hzp

theorem logarithmicOrder_congr_nhds {u v : SurfaceCoord → WithBot ℝ}
    {p : SurfaceCoord} (he : u =ᶠ[𝓝 p] v) : logarithmicOrder u p = logarithmicOrder v p := by
  unfold logarithmicOrder
  congr 1
  ext c
  exact and_congr_right (fun _ => ⟨(fun h => h.congr_nhds he),(fun h => h.congr_nhds he.symm)⟩)

theorem normalLogWeight_upperBound (a : ℝ) (ha : 0 ≤ a) (R : SurfaceCoord → ℝ)
    (x : ℂ) (hR : ContinuousAt R (x,0)) : LogarithmicUpperBound (normalLogWeight a R) (x,0) a := by
  have he : ∀ᶠ z in 𝓝 (x,(0:ℂ)), R z < R (x,0)+1 :=
    hR.tendsto.eventually (eventually_lt_nhds (lt_add_one _))
  obtain ⟨r,hr,hbound⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨R (x,0)+1,r,hr,?_⟩
  intro z hz hzp
  by_cases hs : z.2 = 0
  · simp [normalLogWeight,hs]
  · simp only [normalLogWeight,hs,if_false,WithBot.coe_le_coe]
    have hn : ‖z.2‖ ≤ ‖z-(x,0)‖ := by
      have hh := norm_snd_le (z-(x,0))
      change ‖z.2-0‖ ≤ ‖z-(x,0)‖ at hh
      simpa only [sub_zero] using hh
    have hsq : Complex.normSq z.2 ≤ ‖z-(x,0)‖^2 := by
      rw [Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) hn 2
    have hl := Real.log_le_log (Complex.normSq_pos.mpr hs) hsq
    exact add_le_add (mul_le_mul_of_nonneg_left hl ha) (hbound hz).le

theorem normalLogWeight_no_upperBound (a : ℝ) (R : SurfaceCoord → ℝ) (x : ℂ)
    (hR : ContinuousAt R (x,0)) (c : ℝ) (hac : a < c) :
    ¬ LogarithmicUpperBound (normalLogWeight a R) (x,0) c := by
  rintro ⟨C,r,hr,hbound⟩
  have hp : Tendsto (fun t : ℝ => (x,(t:ℂ))) (𝓝[>] (0:ℝ)) (𝓝 (x,(0:ℂ))) := by
    have h : ContinuousAt (fun t : ℝ => (x,(t:ℂ))) 0 :=
      continuous_const.continuousAt.prodMk Complex.continuous_ofReal.continuousAt
    exact h.tendsto.mono_left nhdsWithin_le_nhds
  have hlog : Tendsto (fun t : ℝ => (2*(a-c))*Real.log t) (𝓝[>] (0:ℝ)) atTop :=
    Real.tendsto_log_nhdsGT_zero.const_mul_atBot_of_neg (by linarith)
  have htop := (hR.tendsto.comp hp).add_atTop hlog
  have hlarge : ∀ᶠ t : ℝ in 𝓝[>] 0, C+1 ≤ R (x,(t:ℂ)) + (2*(a-c))*Real.log t :=
    (tendsto_atTop.mp htop) (C+1)
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < r :=
    (eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds
  have hpositive : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t,ht,hs,hl⟩ := (hpositive.and (hsmall.and hlarge)).exists
  have ht' : 0 < t := ht
  have hn : ‖(x,(t:ℂ))-(x,(0:ℂ))‖ = t := by
    simp [Prod.norm_def,abs_of_pos ht',ht'.le]
  have hz : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht'.ne'
  have hne : (x,(t:ℂ)) ≠ (x,(0:ℂ)) := by
    intro he
    exact hz (congrArg Prod.snd he)
  have hh := hbound (x,(t:ℂ)) (by rw [dist_eq_norm,hn]; exact hs) hne
  simp only [normalLogWeight,hz,if_false,WithBot.coe_le_coe,hn] at hh
  have hnorm : Complex.normSq (t:ℂ) = t^2 := by
    simp [Complex.normSq_eq_norm_sq,abs_of_pos ht']
  rw [hnorm,Real.log_pow] at hh
  norm_num at hh
  nlinarith

theorem normalLogWeight_order (a : ℝ) (ha : 0 ≤ a) (R : SurfaceCoord → ℝ)
    (x : ℂ) (hR : ContinuousAt R (x,0)) : logarithmicOrder (normalLogWeight a R) (x,0) = a := by
  have haMem : a ∈ {c : ℝ | 0 ≤ c ∧ LogarithmicUpperBound (normalLogWeight a R) (x,0) c} :=
    ⟨ha,normalLogWeight_upperBound a ha R x hR⟩
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt ⟨a,haMem⟩
  · intro c hc
    by_contra h
    exact normalLogWeight_no_upperBound a R x hR c (lt_of_not_ge h) hc.2
  · intro c hc
    exact ⟨a,haMem,hc⟩

end
end FailureOfSemipositiveMetricExtension
