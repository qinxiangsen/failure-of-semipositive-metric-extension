import FailureOfSemipositiveMetricExtension.IdealSheafGluedSubscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! The canonical map from the genuinely glued ideal-sheaf quotient is a closed
immersion of schemes, including the stalk-surjectivity condition. -/
namespace FailureOfSemipositiveMetricExtension.IdealSheafGluedSubscheme
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Set Topology
universe u
variable {X : Scheme.{u}} (I : X.IdealSheafData)

instance localInclusion_isClosedImmersion (U : X.affineOpens) :
    IsClosedImmersion (I.glueDataObjι U) := by
  unfold Scheme.IdealSheafData.glueDataObjι
  infer_instance

theorem range_chart (U : X.affineOpens) :
    range (I.glueData.ι U).base = (inclusion I).base ⁻¹' U.1 := by
  ext q
  constructor
  · rintro ⟨x,rfl⟩
    change (I.glueData.ι U ≫ inclusion I).base x ∈ U.1
    rw [chart_inclusion]
    exact ((I.glueDataObjι U).base x).property
  · intro hq
    have hsup : (inclusion I).base q ∈ I.support := by
      exact (range_inclusion I).le ⟨q,rfl⟩
    have hx : (inclusion I).base q ∈ range (I.glueDataObjι U ≫ U.1.ι).base := by
      rw [I.range_glueDataObjι_ι,← I.coe_support_inter]
      exact ⟨hsup,hq⟩
    obtain ⟨x,hx⟩ := hx
    refine ⟨x,inclusion_injective I ?_⟩
    change (I.glueData.ι U ≫ inclusion I).base x = _
    simpa only [chart_inclusion] using hx

theorem image_preimage_chart (U : X.affineOpens) (s : Set (scheme I)) :
    (I.glueDataObjι U).base '' ((I.glueData.ι U).base ⁻¹' s) =
      Subtype.val ⁻¹' ((inclusion I).base '' s) := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨(I.glueData.ι U).base x,hx,?_⟩
    change (I.glueData.ι U ≫ inclusion I).base x = _
    rw [chart_inclusion]
    rfl
  · rintro ⟨q,hq,he⟩
    have hr : q ∈ range (I.glueData.ι U).base := by
      rw [range_chart]
      change (inclusion I).base q ∈ U.1
      rw [he]
      exact y.property
    obtain ⟨x,rfl⟩ := hr
    refine ⟨x,hq,?_⟩
    apply Subtype.ext
    change (I.glueDataObjι U ≫ U.1.ι).base x = y.val
    simpa only [← chart_inclusion,Scheme.comp_base_apply] using he

theorem affineOpens_cover : IsOpenCover (fun U : X.affineOpens => U.1) := by
  apply IsOpenCover.mk
  apply top_le_iff.mp
  intro x _
  obtain ⟨_,⟨U,hU,rfl⟩,hxU,_⟩ :=
    (isBasis_affine_open X).exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact Opens.mem_iSup.mpr ⟨⟨U,hU⟩,hxU⟩

theorem inclusion_isClosedMap : IsClosedMap (inclusion I).base := by
  intro s hs
  apply (affineOpens_cover (X := X)).isClosed_iff_coe_preimage.mpr
  intro U
  rw [← image_preimage_chart]
  exact (I.glueDataObjι U).isClosedEmbedding.isClosedMap _
    (hs.preimage (I.glueData.ι U).base.hom.continuous)

theorem inclusion_isClosedEmbedding : IsClosedEmbedding (inclusion I).base :=
  .of_continuous_injective_isClosedMap (inclusion I).base.hom.continuous
    (inclusion_injective I) (inclusion_isClosedMap I)

instance inclusion_isClosedImmersion : IsClosedImmersion (inclusion I) where
  base_closed := inclusion_isClosedEmbedding I

end
end FailureOfSemipositiveMetricExtension.IdealSheafGluedSubscheme
