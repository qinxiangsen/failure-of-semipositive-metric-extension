import FailureOfSemipositiveMetricExtension.ProjectiveLineDegreeZeroSections

/-! Complex C-infinity sections on the actual projective line are upgraded in
one-dimensional coordinates using the proved Cauchy theorem. This explicitly
bridges the holomorphic structure-sheaf regularity to the analytic bundle APIs. -/
namespace FailureOfSemipositiveMetricExtension.ProjectiveLineBundle
noncomputable section
open FailureOfSemipositiveMetricExtension.ProjectiveLine Set Bundle IsManifold Filter
open scoped Manifold ContDiff Topology

theorem coefficient_analytic_of_complex_smooth (i : Fin 2) (f : Point → ℂ)
    (hf : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ∞ f (chartSet i)) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω f (chartSet i) := by
  have hc : ContDiff ℂ ∞ (fun z => f (param i z)) :=
    ((hf.comp_contMDiff (param_contMDiff i ∞) (fun z => ⟨z,rfl⟩))).contDiff
  have ha : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => f (param i z)) :=
    ((hc.differentiable (by simp)).contDiff).contMDiff
  apply (ha.comp_contMDiffOn (coordinates_contMDiffOn i ω)).congr
  intro d hd
  exact congrArg f (param_coordinates i d hd).symm

def ofHolomorphicSection {d : ℤ} (s : ∀ p : Point, (core d).Fiber p)
    (hs : ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ∞ (fun p => (⟨p,s p⟩ : (core d).TotalSpace))) :
    SectionData d where
  coefficient i p := ((core d).localTriv i ⟨p,s p⟩).2
  analytic i := by
    apply coefficient_analytic_of_complex_smooth
    let e := (core d).localTriv i
    haveI : MemTrivializationAtlas e := ⟨⟨i,rfl⟩⟩
    have hh : ContMDiffOn 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ∞
        (fun p => e (⟨p,s p⟩ : (core d).TotalSpace)) (chartSet i) :=
      e.contMDiffOn.comp hs.contMDiffOn (fun p hp => hp)
    exact contMDiff_snd.comp_contMDiffOn hh
  compatible i j p hp := by
    change gain d i j p * (gain d ((core d).indexAt p) i p * (show ℂ from s p)) =
      gain d ((core d).indexAt p) j p * (show ℂ from s p)
    rw [← mul_assoc,gain_comp d ((core d).indexAt p) i j p
      ⟨⟨(core d).mem_baseSet_at p,hp.1⟩,hp.2⟩]

theorem ofHolomorphicSection_value {d : ℤ} (s : ∀ p : Point, (core d).Fiber p)
    (hs : ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ∞ (fun p => (⟨p,s p⟩ : (core d).TotalSpace)))
    (p : Point) : sectionValue (ofHolomorphicSection s hs) p = s p := by
  change gain d ((core d).indexAt p) ((core d).indexAt p) p * (show ℂ from s p) = s p
  simp [gain,ratio_self]

theorem holomorphic_section_zero (d : ℤ) (hd : d < 0) (s : ∀ p : Point, (core d).Fiber p)
    (hs : ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ∞ (fun p => (⟨p,s p⟩ : (core d).TotalSpace)))
    (p : Point) : s p = 0 := by
  rw [← ofHolomorphicSection_value s hs p]
  exact negative_sectionValue_zero d hd (ofHolomorphicSection s hs) p

theorem holomorphic_section_zero_of_degree_eq_zero (d : ℤ) (hd : d = 0)
    (s : ∀ p : Point, (core d).Fiber p)
    (hs : ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ∞ (fun p => (⟨p,s p⟩ : (core d).TotalSpace)))
    (q : Point) (hq : s q = 0) (p : Point) : s p = 0 := by
  subst d
  have h := degree_zero_sectionValue_constant (ofHolomorphicSection s hs) p q
  rw [ofHolomorphicSection_value,ofHolomorphicSection_value,hq] at h
  exact h

end
end FailureOfSemipositiveMetricExtension.ProjectiveLineBundle
