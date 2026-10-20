import FailureOfSemipositiveMetricExtension.IdealSheafClosedImmersion

/-! A field-valued point whose image lies in a closed subset factors through
its actual globally glued reduced induced subscheme. -/
namespace FailureOfSemipositiveMetricExtension.IdealSheafGluedSubscheme
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Set
universe u
variable {K : Type u} [Field K]

def fieldPoint : Spec (.of K) := ⟨⊥,Ideal.bot_prime⟩

theorem fieldSpectrum_eq (x : Spec (.of K)) : x = fieldPoint := by
  apply PrimeSpectrum.ext
  exact x.asIdeal.eq_bot_or_top.resolve_right x.isPrime.ne_top

variable {X : Scheme.{u}} (Z : Closeds X)

/-- Actual morphism factorization through the closed subscheme, valid over every field. -/
theorem exists_fieldPoint_lift (f : Spec (.of K) ⟶ X)
    (hf : f.base fieldPoint ∈ Z) :
    ∃ g : Spec (.of K) ⟶ scheme (Scheme.IdealSheafData.vanishingIdeal Z),
      g ≫ inclusion (Scheme.IdealSheafData.vanishingIdeal Z) = f := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  obtain ⟨_,⟨U,hU,rfl⟩,hxU,_⟩ :=
    (isBasis_affine_open X).exists_subset_of_mem_open (Set.mem_univ (f.base fieldPoint)) isOpen_univ
  let V : X.affineOpens := ⟨U,hU⟩
  have hrange : range f.base ⊆ range V.1.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x,rfl⟩
    simpa only [fieldSpectrum_eq x] using hxU
  let fU := IsOpenImmersion.lift V.1.ι f hrange
  have hfac : fU ≫ V.1.ι = f := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨φ,hφ⟩ := Spec.map_surjective (fU ≫ hU.isoSpec.hom)
  have hφfac : Spec.map φ ≫ hU.fromSpec = f := by
    rw [hφ]
    change (fU ≫ hU.isoSpec.hom) ≫ (hU.isoSpec.inv ≫ V.1.ι) = f
    simpa only [Category.assoc,Iso.hom_inv_id_assoc] using hfac
  have hker : I.ideal V ≤ RingHom.ker φ.hom := by
    intro a ha
    change a ∈ PrimeSpectrum.vanishingIdeal (hU.fromSpec.base ⁻¹' (Z : Set X)) at ha
    have hmem : (Spec.map φ).base fieldPoint ∈ hU.fromSpec.base ⁻¹' (Z : Set X) := by
      change (Spec.map φ ≫ hU.fromSpec).base fieldPoint ∈ Z
      simpa only [hφfac] using hf
    exact (PrimeSpectrum.mem_vanishingIdeal _ _).mp ha _ hmem
  let ψ := CommRingCat.ofHom (Ideal.Quotient.lift (I.ideal V) φ.hom hker)
  refine ⟨Spec.map ψ ≫ I.glueData.ι V,?_⟩
  rw [Category.assoc,chart_inclusion,Scheme.IdealSheafData.glueDataObjι_ι,
    ← Category.assoc,← Spec.map_comp]
  exact hφfac

/-- Uniqueness is the actual categorical monomorphism property of a closed immersion. -/
theorem existsUnique_fieldPoint_lift (f : Spec (.of K) ⟶ X)
    (hf : f.base fieldPoint ∈ Z) :
    ∃! g : Spec (.of K) ⟶ scheme (Scheme.IdealSheafData.vanishingIdeal Z),
      g ≫ inclusion (Scheme.IdealSheafData.vanishingIdeal Z) = f := by
  obtain ⟨g,hg⟩ := exists_fieldPoint_lift Z f hf
  refine ⟨g,hg,fun g' hg' => ?_⟩
  exact (cancel_mono (inclusion (Scheme.IdealSheafData.vanishingIdeal Z))).mp (hg'.trans hg.symm)

end
end FailureOfSemipositiveMetricExtension.IdealSheafGluedSubscheme
