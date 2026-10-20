import Mathlib.AlgebraicGeometry.IdealSheaf

/-! The actual scheme obtained by gluing the affine quotients of an ideal sheaf,
with its canonical morphism to the ambient scheme. This makes explicit the
morphism left implicit in mathlib's `IdealSheafData.glueData`. -/
namespace FailureOfSemipositiveMetricExtension.IdealSheafGluedSubscheme
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Set
universe u
variable {X : Scheme.{u}} (I : X.IdealSheafData)

abbrev scheme : Scheme := I.glueData.glued

def inclusion : scheme I ⟶ X := by
  fapply Multicoequalizer.desc
  · exact fun U => I.glueDataObjι U ≫ U.1.ι
  rintro ⟨U,V⟩
  change pullback.fst _ _ ≫ (I.glueDataObjι U ≫ U.1.ι) =
    (I.glueDataT U V ≫ pullback.fst _ _) ≫ (I.glueDataObjι V ≫ V.1.ι)
  rw [Category.assoc,Scheme.IdealSheafData.glueDataT_fst_assoc,pullback.condition_assoc]
  simp

@[simp,reassoc] theorem chart_inclusion (U : X.affineOpens) :
    I.glueData.ι U ≫ inclusion I = I.glueDataObjι U ≫ U.1.ι :=
  Multicoequalizer.π_desc _ _ _ _ _

theorem range_inclusion : range (inclusion I).base = I.support := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    obtain ⟨U,z,rfl⟩ := I.glueData.ι_jointly_surjective y
    have h : (inclusion I).base ((I.glueData.ι U).base z) ∈
        range (I.glueDataObjι U ≫ U.1.ι).base := by
      rw [← chart_inclusion]
      exact ⟨z,rfl⟩
    rw [I.range_glueDataObjι_ι,← I.coe_support_inter] at h
    exact h.1
  · intro hx
    obtain ⟨_,⟨U,hU,rfl⟩,hxU,_⟩ :=
      (isBasis_affine_open X).exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    let V : X.affineOpens := ⟨U,hU⟩
    have h : x ∈ range (I.glueDataObjι V ≫ V.1.ι).base := by
      rw [I.range_glueDataObjι_ι,← I.coe_support_inter]
      exact ⟨hx,hxU⟩
    obtain ⟨z,hz⟩ := h
    refine ⟨(I.glueData.ι V).base z,?_⟩
    change (I.glueData.ι V ≫ inclusion I).base z = x
    simpa only [chart_inclusion] using hz

instance inclusion_surjectiveOnStalks : SurjectiveOnStalks (inclusion I) := by
  apply IsLocalAtSource.of_openCover (P := @SurjectiveOnStalks) I.glueData.openCover
  intro U
  change SurjectiveOnStalks (I.glueData.ι U ≫ inclusion I)
  rw [chart_inclusion]
  infer_instance

/-- The glued inclusion identifies no distinct points. -/
theorem inclusion_injective : Function.Injective (inclusion I).base := by
  intro x y h
  obtain ⟨U,x,rfl⟩ := I.glueData.ι_jointly_surjective x
  obtain ⟨V,y,rfl⟩ := I.glueData.ι_jointly_surjective y
  have he : (I.glueDataObjι U ≫ U.1.ι).base x = (I.glueDataObjι V ≫ V.1.ι).base y := by
    simpa only [← chart_inclusion,Scheme.comp_base_apply] using h
  have hxV : ((I.glueDataObjι U).base x).val ∈ V.1 := by
    rw [show ((I.glueDataObjι U).base x).val = ((I.glueDataObjι V).base y).val from he]
    exact ((I.glueDataObjι V).base y).property
  have hx : x ∈ range (pullback.fst (I.glueDataObjι U)
      (X.homOfLE (inf_le_left (b := V.1)))).base := by
    rw [IsOpenImmersion.range_pullback_fst_of_right]
    change (I.glueDataObjι U).base x ∈ range (X.homOfLE (inf_le_left (b := V.1))).base
    refine ⟨⟨_,((I.glueDataObjι U).base x).property,hxV⟩,?_⟩
    apply Subtype.ext
    exact X.homOfLE_apply _ _
  obtain ⟨z,hz⟩ := hx
  apply (I.glueData.ι_eq_iff U V x y).mpr
  refine ⟨z,hz,?_⟩
  apply (I.glueDataObjι V ≫ V.1.ι).isEmbedding.injective
  change (I.glueDataT U V ≫ pullback.fst _ _ ≫ I.glueDataObjι V ≫ V.1.ι).base z = _
  rw [Scheme.IdealSheafData.glueDataT_fst_assoc]
  rw [X.homOfLE_ι,← X.homOfLE_ι (inf_le_left (a := U.1) (b := V.1)),← pullback.condition_assoc]
  change (I.glueDataObjι U ≫ U.1.ι).base ((pullback.fst (I.glueDataObjι U) (X.homOfLE (inf_le_left (b := V.1)))).base z) = _
  rw [hz]
  exact he

end
end FailureOfSemipositiveMetricExtension.IdealSheafGluedSubscheme
