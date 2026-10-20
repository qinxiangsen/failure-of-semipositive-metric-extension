import FailureOfSemipositiveMetricExtension.ProjectivePlaneAtlas
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-! The standard affine atlas defines an actual complex-analytic manifold structure
on mathlib's projectivization of `Fin 3 → ℂ`. Hausdorffness and compactness are separate
properties and are not presumed by this chart-compatibility construction. -/

noncomputable section

namespace FailureOfSemipositiveMetricExtension.ProjectivePlane

open Set
open scoped Manifold ContDiff

/-- Exactly the three constructed homeomorphisms form the installed atlas. -/
theorem mem_atlas_iff (e : PartialHomeomorph Point (ℂ × ℂ)) :
    e ∈ atlas (ℂ × ℂ) Point ↔ ∃ i, e = homeomorphChart i := by
  change (e ∈ ⋃ (f : PartialEquiv Point (ℂ × ℂ)) (hf : f ∈ atlasCore.atlas),
    {atlasCore.partialHomeomorph f hf}) ↔ _
  simp only [mem_iUnion,mem_singleton_iff]
  constructor
  · rintro ⟨f,⟨i,rfl⟩,rfl⟩
    exact ⟨i,rfl⟩
  · rintro ⟨i,rfl⟩
    exact ⟨partialChart i,⟨i,rfl⟩,rfl⟩

theorem atlas_contDiffOn (n : WithTop ℕ∞)
    (e e' : PartialHomeomorph Point (ℂ × ℂ))
    (he : e ∈ atlas (ℂ × ℂ) Point) (he' : e' ∈ atlas (ℂ × ℂ) Point) :
    ContDiffOn ℂ n (e.symm.trans e') (e.symm.trans e').source := by
  rcases (mem_atlas_iff e).mp he with ⟨i,rfl⟩
  rcases (mem_atlas_iff e').mp he' with ⟨j,rfl⟩
  change ContDiffOn ℂ n ((partialChart i).symm.trans (partialChart j))
    ((partialChart i).symm.trans (partialChart j)).source
  rw [partialChart_transition_source]
  exact (transition_contDiffOn i j n).congr (partialChart_transition_apply i j)

/-- Complex manifold compatibility is verified at every regularity, including analytic. -/
instance instIsManifoldPoint (n : WithTop ℕ∞) : IsManifold 𝓘(ℂ, ℂ × ℂ) n Point := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  simpa using atlas_contDiffOn n e e' he he'

theorem complex_analytic_manifold : IsManifold 𝓘(ℂ, ℂ × ℂ) ω Point := inferInstance

end FailureOfSemipositiveMetricExtension.ProjectivePlane
