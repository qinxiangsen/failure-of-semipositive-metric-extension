import FailureOfSemipositiveMetricExtension.BlowupAtlas
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
The atlas-built incidence blow-up has complex-analytic transition maps, and hence
an actual mathlib `IsManifold` structure, including analytic regularity `ω`.
No Hausdorffness, properness, or global projective family is
asserted merely by installing this chart-compatibility structure.
-/

noncomputable section

namespace FailureOfSemipositiveMetricExtension.Blowup

open Set
open scoped Manifold ContDiff

/-- The rational transition is complex `C^n` on its overlap for every regularity,
including analytic regularity. -/
theorem transition_contDiffOn (n : WithTop ℕ∞) : ContDiffOn ℂ n transition overlap := by
  exact (contDiff_fst.mul contDiff_snd).contDiffOn.prodMk
    (contDiff_snd.contDiffOn.inv (fun q hq => hq))

/-- The installed atlas has exactly the two constructed partial homeomorphisms. -/
theorem mem_atlas_iff (e : PartialHomeomorph Point (ℂ × ℂ)) :
    e ∈ atlas (ℂ × ℂ) Point ↔ e = homeomorphChartX ∨ e = homeomorphChartY := by
  change (e ∈ ⋃ (f : PartialEquiv Point (ℂ × ℂ)) (hf : f ∈ atlasCore.atlas),
    {atlasCore.partialHomeomorph f hf}) ↔ _
  simp only [mem_iUnion,mem_singleton_iff]
  constructor
  · rintro ⟨f,hf,rfl⟩
    change f = partialChartX ∨ f = partialChartY at hf
    rcases hf with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨partialChartX,by simp [atlasCore],rfl⟩
    · exact ⟨partialChartY,by simp [atlasCore],rfl⟩

/-- Compatibility of all charts has been proved from the explicit transition. -/
theorem atlas_contDiffOn (n : WithTop ℕ∞)
    (e e' : PartialHomeomorph Point (ℂ × ℂ))
    (he : e ∈ atlas (ℂ × ℂ) Point) (he' : e' ∈ atlas (ℂ × ℂ) Point) :
    ContDiffOn ℂ n (e.symm.trans e') (e.symm.trans e').source := by
  rcases (mem_atlas_iff e).mp he with rfl | rfl <;>
    rcases (mem_atlas_iff e').mp he' with rfl | rfl
  · exact contDiffOn_id.congr (fun q _ => transitionXX_apply q)
  · change ContDiffOn ℂ n (partialChartX.symm.trans partialChartY)
      (partialChartX.symm.trans partialChartY).source
    rw [transitionXY_source]
    exact (transition_contDiffOn n).congr transitionXY_apply
  · change ContDiffOn ℂ n (partialChartY.symm.trans partialChartX)
      (partialChartY.symm.trans partialChartX).source
    rw [transitionYX_source]
    exact (transition_contDiffOn n).congr transitionYX_apply
  · exact contDiffOn_id.congr (fun q _ => transitionYY_apply q)

/-- The incidence blow-up with its verified atlas is a complex manifold in mathlib's
chart-compatibility sense, at every regularity including complex analytic. -/
instance instIsManifoldPoint (n : WithTop ℕ∞) : IsManifold 𝓘(ℂ, ℂ × ℂ) n Point := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  simpa using atlas_contDiffOn n e e' he he'

/-- Explicit analytic-regularity specialization of the manifold instance. -/
theorem complex_analytic_manifold : IsManifold 𝓘(ℂ, ℂ × ℂ) ω Point := inferInstance

end FailureOfSemipositiveMetricExtension.Blowup
