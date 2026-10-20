import Mathlib.Analysis.Complex.Liouville

/-! Analytic, rather than numerical, vanishing for the two-chart transition of
negative-degree line bundles on the actual complex projective line. -/
namespace FailureOfSemipositiveMetricExtension
noncomputable section
open Set Filter
open scoped Topology

/-- The two entire coefficients of a negative-degree projective-line section
must vanish. This uses the proved mathlib Liouville theorem, with no external axiom. -/
theorem negative_degree_entire_pair (k : ℕ) (f₀ f₁ : ℂ → ℂ)
    (h₀ : Differentiable ℂ f₀) (h₁ : Continuous f₁)
    (htrans : ∀ z : ℂ, z ≠ 0 → f₀ z = (z⁻¹)^(k+1) * f₁ z⁻¹) :
    (∀ z, f₀ z = 0) ∧ (∀ z, f₁ z = 0) := by
  have hinv : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [Metric.cobounded_eq_cocompact] using
      (tendsto_inv₀_cobounded : Tendsto (fun z : ℂ => z⁻¹) (Bornology.cobounded ℂ) (𝓝 0))
  have hlim : Tendsto (fun z : ℂ => (z⁻¹)^(k+1) * f₁ z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [zero_pow (Nat.succ_ne_zero k),zero_mul] using
      (hinv.pow (k+1)).mul (h₁.continuousAt.tendsto.comp hinv)
  have hzero : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 := isCompact_singleton.compl_mem_cocompact
  have hf₀ : ∀ z, f₀ z = 0 := by
    intro z
    apply h₀.apply_eq_of_tendsto_cocompact z
    apply hlim.congr'
    filter_upwards [hzero] with w hw
    exact (htrans w hw).symm
  have hf₁ : EqOn f₁ (fun _ => 0) ({(0:ℂ)}ᶜ) := by
    intro z hz
    have hz' : z ≠ 0 := hz
    have hh := htrans z⁻¹ (inv_ne_zero hz')
    rw [hf₀,inv_inv] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left (pow_ne_zero _ hz')
  have hall : f₁ = fun _ => 0 := Continuous.ext_on (dense_compl_singleton (0:ℂ)) h₁ continuous_const hf₁
  exact ⟨hf₀,fun z => congrFun hall z⟩

end
end FailureOfSemipositiveMetricExtension
