import FailureOfSemipositiveMetricExtension.BlowupBundleSections
import FailureOfSemipositiveMetricExtension.BlowupProper

/-! Fibre generation is open for the actual glued line-bundle sections. Properness
turns generation on the exceptional fibre into generation over an affine base
neighbourhood. No global four-point surface is postulated. -/
namespace FailureOfSemipositiveMetricExtension.BlowupLineBundle
noncomputable section
open FailureOfSemipositiveMetricExtension.Blowup FailureOfSemipositiveMetricExtension.BlowupSections Set

def nonzeroLocus {k : ℕ} (a : SectionData k) : Set Point :=
  {p | sectionValue a p ≠ 0}

theorem nonzeroLocus_eq {k : ℕ} (a : SectionData k) :
    nonzeroLocus a =
      (fun q : ℂ × ℂ => X q.1 q.2) '' {q | a.x q ≠ 0} ∪
      (fun q : ℂ × ℂ => Y q.1 q.2) '' {q | a.y q ≠ 0} := by
  ext p
  constructor
  · intro hp
    rcases charts_cover p with ⟨r,s,rfl⟩ | ⟨r,s,rfl⟩
    · exact Or.inl ⟨(r,s),by simpa [nonzeroLocus,sectionValue_zero_iff,zeroAt_X_iff] using hp,rfl⟩
    · exact Or.inr ⟨(r,s),by simpa [nonzeroLocus,sectionValue_zero_iff,zeroAt_Y_iff] using hp,rfl⟩
  · rintro (⟨q,hq,rfl⟩ | ⟨q,hq,rfl⟩)
    · simpa [nonzeroLocus,sectionValue_zero_iff,zeroAt_X_iff] using hq
    · simpa [nonzeroLocus,sectionValue_zero_iff,zeroAt_Y_iff] using hq

theorem nonzeroLocus_isOpen {k : ℕ} (a : SectionData k) : IsOpen (nonzeroLocus a) := by
  rw [nonzeroLocus_eq]
  exact (X_isOpenEmbedding.isOpenMap _ (isOpen_ne.preimage a.x_holomorphic.continuous)).union
    (Y_isOpenEmbedding.isOpenMap _ (isOpen_ne.preimage a.y_holomorphic.continuous))

def generatingLocus {ι : Type*} {k : ℕ} (a : ι → SectionData k) : Set Point :=
  {p | ∃ i, sectionValue (a i) p ≠ 0}

theorem generatingLocus_isOpen {ι : Type*} {k : ℕ} (a : ι → SectionData k) :
    IsOpen (generatingLocus a) := by
  have heq : generatingLocus a = ⋃ i, nonzeroLocus (a i) := by
    ext p; simp [generatingLocus,nonzeroLocus]
  rw [heq]
  exact isOpen_iUnion (fun i => nonzeroLocus_isOpen (a i))

/-- Properness upgrades exceptional-fibre generation to a full base neighbourhood. -/
theorem generation_over_base_neighborhood {ι : Type*} {k : ℕ} (a : ι → SectionData k)
    (h : ∀ p : Point, projection p = 0 → ∃ i, sectionValue (a i) p ≠ 0) :
    ∃ V : Set Plane, IsOpen V ∧ (0 : Plane) ∈ V ∧
      ∀ p : Point, projection p ∈ V → ∃ i, sectionValue (a i) p ≠ 0 := by
  obtain ⟨V,hV,h0,hsub⟩ := fiber_neighborhood 0 (generatingLocus a)
    (generatingLocus_isOpen a) (by intro p hp; exact h p hp)
  exact ⟨V,hV,h0,fun p hp => hsub hp⟩

/-- All four central local systems generate throughout a common affine neighbourhood. -/
theorem central_generation_over_base_neighborhood :
    ∃ V : Set Plane, IsOpen V ∧ (0 : Plane) ∈ V ∧
      ∀ p : Point, projection p ∈ V →
        (∃ i, sectionValue (cubicSystem₁ i) p ≠ 0) ∧
        (∃ i, sectionValue (cubicSystem₂ i) p ≠ 0) ∧
        (∃ i, sectionValue (cubicSystem₃ i) p ≠ 0) ∧
        (∃ i, sectionValue (cubicSystem₄ i) p ≠ 0) := by
  let U := generatingLocus cubicSystem₁ ∩ generatingLocus cubicSystem₂ ∩
    generatingLocus cubicSystem₃ ∩ generatingLocus cubicSystem₄
  have hU : IsOpen U := (((generatingLocus_isOpen cubicSystem₁).inter
    (generatingLocus_isOpen cubicSystem₂)).inter (generatingLocus_isOpen cubicSystem₃)).inter
    (generatingLocus_isOpen cubicSystem₄)
  obtain ⟨V,hV,h0,hsub⟩ := fiber_neighborhood 0 U hU (by
    intro p hp
    obtain ⟨h1,h2,h3,h4⟩ := central_actual_sections_no_exceptional_basepoint p hp
    exact ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩)
  refine ⟨V,hV,h0,fun p hp => ?_⟩
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := hsub hp
  exact ⟨h1,h2,h3,h4⟩

open FailureOfSemipositiveMetricExtension.PencilSections in
theorem nearby_generation_over_base_neighborhood (t : ℂ) (ht : t ≠ 0) :
    ∃ V : Set Plane, IsOpen V ∧ (0 : Plane) ∈ V ∧
      ∀ p : Point, projection p ∈ V →
        (∃ i, sectionValue (pencilSystem₁ t i) p ≠ 0) ∧
        (∃ i, sectionValue (pencilSystem₂ t i) p ≠ 0) ∧
        (∃ i, sectionValue (pencilSystem₃ t i) p ≠ 0) ∧
        (∃ i, sectionValue (pencilSystem₄ t i) p ≠ 0) := by
  let U := generatingLocus (pencilSystem₁ t) ∩ generatingLocus (pencilSystem₂ t) ∩
    generatingLocus (pencilSystem₃ t) ∩ generatingLocus (pencilSystem₄ t)
  have hU : IsOpen U := (((generatingLocus_isOpen (pencilSystem₁ t)).inter
    (generatingLocus_isOpen (pencilSystem₂ t))).inter
    (generatingLocus_isOpen (pencilSystem₃ t))).inter (generatingLocus_isOpen (pencilSystem₄ t))
  obtain ⟨V,hV,h0,hsub⟩ := fiber_neighborhood 0 U hU (by
    intro p hp
    obtain ⟨h1,h2,h3,h4⟩ := nearby_actual_sections_no_exceptional_basepoint t ht p hp
    exact ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩)
  refine ⟨V,hV,h0,fun p hp => ?_⟩
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := hsub hp
  exact ⟨h1,h2,h3,h4⟩
end
end FailureOfSemipositiveMetricExtension.BlowupLineBundle
