import FailureOfSemipositiveMetricExtension.ProjectivePlaneManifold
import FailureOfSemipositiveMetricExtension.ProjectivePlaneCompact
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
The actual starting family `ℙ² × ℂ → ℂ` and the four moving centres in the paper.
Its projection is proper and analytic; its four centre sections are analytic,
closed, pairwise disjoint, and sections of the projection. This is the family
before blowing up, not a claim that the global simultaneous blow-up is constructed.
-/

noncomputable section

namespace FailureOfSemipositiveMetricExtension.ProjectivePlane

open Set IsManifold
open scoped Manifold ContDiff

/-- Affine chart parametrizations are analytic as maps into the constructed manifold. -/
theorem param_contMDiff (i : Fin 3) (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) n (param i) := by
  have he : homeomorphChart i ∈ maximalAtlas 𝓘(ℂ, ℂ × ℂ) n Point :=
    IsManifold.subset_maximalAtlas ((mem_atlas_iff _).mpr ⟨i,rfl⟩)
  exact contMDiffOn_univ.mp (contMDiffOn_symm_of_mem_maximalAtlas he)

@[simp] theorem P₁_eq_param : Coordinates.P₁ = param 0 (0,0) := rfl
@[simp] theorem P₂_eq_param : Coordinates.P₂ = param 1 (0,0) := rfl
@[simp] theorem P₃_eq_param (t : ℂ) : Coordinates.P₃ t = param 0 (1,t) := rfl
@[simp] theorem P₄_eq_param : Coordinates.P₄ = param 2 (0,0) := rfl

/-- The moving point `[1:1:t]` is genuinely analytic in the constructed projective plane. -/
theorem movingPoint_contMDiff (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ, ℂ × ℂ) n Coordinates.P₃ := by
  change ContMDiff 𝓘(ℂ) 𝓘(ℂ, ℂ × ℂ) n (fun t => param 0 (1,t))
  exact (param_contMDiff 0 n).comp ((contDiff_const.prodMk contDiff_id).contMDiff)

/-- The ambient product family before the blow-up. -/
abbrev Family := Point × ℂ

def familyProjection : Family → ℂ := Prod.snd

theorem familyProjection_continuous : Continuous familyProjection := continuous_snd

theorem familyProjection_contMDiff (n : WithTop ℕ∞) :
    ContMDiff (𝓘(ℂ, ℂ × ℂ).prod 𝓘(ℂ)) 𝓘(ℂ) n familyProjection := contMDiff_snd

/-- The compact projective factor makes the ambient family a genuine proper family. -/
theorem familyProjection_isProperMap : IsProperMap familyProjection := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨familyProjection_continuous,?_⟩
  intro K hK
  have heq : familyProjection ⁻¹' K = (univ : Set Point) ×ˢ K := by
    ext p; simp [familyProjection]
  rw [heq]
  exact isCompact_univ.prod hK

/-- The four specified centres, with the third one varying with the parameter. -/
def centre : Fin 4 → ℂ → Point
  | 0, _ => Coordinates.P₁
  | 1, _ => Coordinates.P₂
  | 2, t => Coordinates.P₃ t
  | 3, _ => Coordinates.P₄

theorem centre_contMDiff (i : Fin 4) (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ, ℂ × ℂ) n (centre i) := by
  fin_cases i
  · exact contMDiff_const
  · exact contMDiff_const
  · exact movingPoint_contMDiff n
  · exact contMDiff_const

theorem centre_continuous (i : Fin 4) : Continuous (centre i) :=
  (centre_contMDiff i 0).continuous

/-- The actual section maps into the product family. -/
def centreSection (i : Fin 4) (t : ℂ) : Family := (centre i t,t)

@[simp] theorem familyProjection_centreSection (i : Fin 4) (t : ℂ) :
    familyProjection (centreSection i t) = t := rfl

theorem centreSection_contMDiff (i : Fin 4) (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ) (𝓘(ℂ, ℂ × ℂ).prod 𝓘(ℂ)) n (centreSection i) :=
  (centre_contMDiff i n).prodMk contMDiff_id

theorem centreSection_continuous (i : Fin 4) : Continuous (centreSection i) :=
  (centreSection_contMDiff i 0).continuous

theorem centres_pairwise_distinct (t : ℂ) : Function.Injective (fun i => centre i t) := by
  intro i j hij
  have hd := Coordinates.four_projective_points_distinct t
  fin_cases i <;> fin_cases j <;> simp_all [centre]

/-- The four global centre sections are pairwise disjoint as subsets of the actual family. -/
theorem centreSection_ranges_disjoint (i j : Fin 4) (hij : i ≠ j) :
    Disjoint (range (centreSection i)) (range (centreSection j)) :=
  Coordinates.disjoint_graphs_of_pointwise_ne (centre i) (centre j)
    (fun t h => hij (centres_pairwise_distinct t h))

/-- Every centre section is a closed subset of the actual product family. -/
theorem centreSection_range_isClosed (i : Fin 4) : IsClosed (range (centreSection i)) := by
  have heq : range (centreSection i) = {p : Family | p.1 = centre i p.2} := by
    ext p
    constructor
    · rintro ⟨t,rfl⟩
      rfl
    · intro hp
      exact ⟨p.2,Prod.ext hp.symm rfl⟩
  rw [heq]
  exact isClosed_eq continuous_fst ((centre_continuous i).comp continuous_snd)

end FailureOfSemipositiveMetricExtension.ProjectivePlane
