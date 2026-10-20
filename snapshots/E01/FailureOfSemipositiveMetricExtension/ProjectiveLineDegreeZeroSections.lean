import FailureOfSemipositiveMetricExtension.ProjectiveLineNegativeSections

/-! Actual analytic O(0) sections are constant, proved from their genuine
standard projective-line transition law and mathlib's Liouville theorem. -/
namespace FailureOfSemipositiveMetricExtension.ProjectiveLineBundle
noncomputable section
open FailureOfSemipositiveMetricExtension.ProjectiveLine Set Bundle IsManifold Filter
open scoped Manifold ContDiff Topology

theorem degree_zero_chartCoefficient_constant (s : SectionData 0) :
    ∀ i z, chartCoefficient s i z = chartCoefficient s 1 0 := by
  have hinv : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [Metric.cobounded_eq_cocompact] using
      (tendsto_inv₀_cobounded : Tendsto (fun z : ℂ => z⁻¹) (Bornology.cobounded ℂ) (𝓝 0))
  have hzero : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 := isCompact_singleton.compl_mem_cocompact
  have h0 : ∀ z, chartCoefficient s 0 z = chartCoefficient s 1 0 := by
    intro z
    apply ((chartCoefficient_contDiff s 0).differentiable (by simp)).apply_eq_of_tendsto_cocompact z
    apply (((chartCoefficient_contDiff s 1).continuous.continuousAt.tendsto).comp hinv).congr'
    filter_upwards [hzero] with w hw
    simpa only [zpow_zero,one_mul] using (chartCoefficient_transition s w hw).symm
  have h1 : EqOn (chartCoefficient s 1) (fun _ => chartCoefficient s 1 0) ({(0:ℂ)}ᶜ) := by
    intro z hz
    have hz' : z ≠ 0 := hz
    have h := chartCoefficient_transition s z⁻¹ (inv_ne_zero hz')
    rw [h0,inv_inv,zpow_zero,one_mul] at h
    exact h.symm
  have hall := Continuous.ext_on (dense_compl_singleton (0:ℂ))
    (chartCoefficient_contDiff s 1).continuous continuous_const h1
  intro i z
  fin_cases i
  · exact h0 z
  · exact congrFun hall z

theorem degree_zero_sectionValue_constant (s : SectionData 0) (p q : Point) :
    (show ℂ from sectionValue s p) = (show ℂ from sectionValue s q) := by
  have hc (r : Point) : (show ℂ from sectionValue s r) = chartCoefficient s 1 0 := by
    let i := (core 0).indexAt r
    obtain ⟨z,hz⟩ := (core 0).mem_baseSet_at r
    change s.coefficient i r = _
    rw [← hz]
    exact degree_zero_chartCoefficient_constant s i z
  exact (hc p).trans (hc q).symm

/-- A single zero forces every value of a genuine analytic O(0) section to vanish. -/
theorem analytic_degree_zero_section_zero_of_zero (s : ∀ p : Point, (core 0).Fiber p)
    (hs : ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ω (fun p => (⟨p,s p⟩ : (core 0).TotalSpace)))
    (q : Point) (hq : s q = 0) (p : Point) : s p = 0 := by
  have h := degree_zero_sectionValue_constant (ofAnalyticSection s hs) p q
  rw [ofAnalyticSection_value,ofAnalyticSection_value,hq] at h
  exact h

/-- Transport-free interface when a computed integer degree is proved to be zero. -/
theorem analytic_section_zero_of_degree_eq_zero (d : ℤ) (hd : d = 0)
    (s : ∀ p : Point, (core d).Fiber p)
    (hs : ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ω (fun p => (⟨p,s p⟩ : (core d).TotalSpace)))
    (q : Point) (hq : s q = 0) (p : Point) : s p = 0 := by
  subst d
  exact analytic_degree_zero_section_zero_of_zero s hs q hq p

end
end FailureOfSemipositiveMetricExtension.ProjectiveLineBundle
