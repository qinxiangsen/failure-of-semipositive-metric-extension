import FailureOfSemipositiveMetricExtension.MultiplierGerms

/-! Actual subsheaves of holomorphic functions specified by local-ring ideals.
Restriction and the sheaf locality condition are proved, not stored as hypotheses. -/
namespace FailureOfSemipositiveMetricExtension.Multiplier
noncomputable section
open Set TopologicalSpace Opposite CategoryTheory Manifold
open scoped Manifold ContDiff

variable (M : Type) [TopologicalSpace M] [ChartedSpace Coord M]

def holomorphicPredicate : TopCat.LocalPredicate (fun _ : TopCat.of M => ℂ) :=
  (contDiffWithinAt_localInvariantProp (I := 𝓘(ℂ,Coord)) (I' := 𝓘(ℂ)) ∞).localPredicate M ℂ

/-- Sections whose actual germs belong to the prescribed local-ring ideals. -/
def idealSections (I : ∀ p : M, Ideal (Stalk M p)) (U : Opens M) :
    Ideal C^∞⟮𝓘(ℂ,Coord),U;𝓘(ℂ),ℂ⟯ where
  carrier := {f | ∀ (p : M) (hp : p ∈ U), (sheaf M).presheaf.germ U p hp f ∈ I p}
  zero_mem' := by intro p hp; rw [map_zero]; exact (I p).zero_mem
  add_mem' := by intro f g hf hg p hp; rw [map_add]; exact (I p).add_mem (hf p hp) (hg p hp)
  smul_mem' := by
    intro f g hg p hp
    change (sheaf M).presheaf.germ U p hp (f*g) ∈ I p
    rw [map_mul]
    exact (I p).mul_mem_left _ (hg p hp)

def idealLocalPredicate (I : ∀ p : M, Ideal (Stalk M p)) :
    TopCat.LocalPredicate (fun _ : TopCat.of M => ℂ) where
  pred {U} f := ∃ hf : ContMDiff 𝓘(ℂ,Coord) 𝓘(ℂ) ∞ f,
    (⟨f,hf⟩ : C^∞⟮𝓘(ℂ,Coord),U;𝓘(ℂ),ℂ⟯) ∈ idealSections M I U
  res {U V} i f h := by
    obtain ⟨hf,hi⟩ := h
    refine ⟨(holomorphicPredicate M).res i f hf,?_⟩
    intro p hp
    have hg : (sheaf M).presheaf.germ U p hp
        (⟨fun x => f (Set.inclusion i.le x),(holomorphicPredicate M).res i f hf⟩ : C^∞⟮𝓘(ℂ,Coord),U;𝓘(ℂ),ℂ⟯) =
        (sheaf M).presheaf.germ V p (i.le hp) ⟨f,hf⟩ := by
      apply (sheaf M).presheaf.germ_ext U hp (𝟙 U) i
      apply Subtype.ext
      rfl
    have H := hg.symm ▸ hi p (i.le hp)
    convert H using 1
  locality {U} f h := by
    have hf : ContMDiff 𝓘(ℂ,Coord) 𝓘(ℂ) ∞ f := by
      apply (holomorphicPredicate M).locality f
      intro p
      obtain ⟨V,hp,i,hV⟩ := h p
      exact ⟨V,hp,i,hV.1⟩
    refine ⟨hf,?_⟩
    intro p hp
    obtain ⟨V,hpV,i,hV⟩ := h ⟨p,hp⟩
    obtain ⟨hfV,hiV⟩ := hV
    have hg : (sheaf M).presheaf.germ U p hp ⟨f,hf⟩ =
        (sheaf M).presheaf.germ V p hpV
          (⟨fun x => f (Set.inclusion i.le x),hfV⟩ : C^∞⟮𝓘(ℂ,Coord),V;𝓘(ℂ),ℂ⟯) := by
      apply (sheaf M).presheaf.germ_ext V hpV i (𝟙 V)
      apply Subtype.ext
      rfl
    rw [hg]
    exact hiV p hpV

/-- Genuine sheaf object with restriction maps and verified unique gluing. -/
def idealSheaf (I : ∀ p : M, Ideal (Stalk M p)) : TopCat.Sheaf (Type) (TopCat.of M) :=
  TopCat.subsheafToTypes (idealLocalPredicate M I)

theorem idealSheaf_eq_of_stalk_ideals {I J : ∀ p : M, Ideal (Stalk M p)}
    (h : ∀ p, I p = J p) : idealSheaf M I = idealSheaf M J := by
  have : I = J := funext h
  rw [this]

/-- Natural inclusion into the actual holomorphic structure sheaf (underlying types). -/
def idealSheafInclusion (I : ∀ p : M, Ideal (Stalk M p)) :
    (idealSheaf M I).presheaf ⟶ (smoothSheaf 𝓘(ℂ,Coord) 𝓘(ℂ) M ℂ).presheaf where
  app _ f := ⟨f.1,f.2.choose⟩
  naturality := by
    intro U V i
    rfl

theorem idealSheafInclusion_injective (I : ∀ p : M, Ideal (Stalk M p))
    (U : Opens M) : Function.Injective ((idealSheafInclusion M I).app (op U)) := by
  intro f g h
  apply Subtype.ext
  exact congrArg (fun a : C^∞⟮𝓘(ℂ,Coord),U;𝓘(ℂ),ℂ⟯ => a.val) h

theorem idealSections_restrict (I : ∀ p : M, Ideal (Stalk M p))
    (U V : Opens M) (i : U ⟶ V) (f : C^∞⟮𝓘(ℂ,Coord),V;𝓘(ℂ),ℂ⟯)
    (hf : f ∈ idealSections M I V) :
    (sheaf M).presheaf.map i.op f ∈ idealSections M I U := by
  intro p hp
  have h := (sheaf M).presheaf.germ_res i p hp
  change ((sheaf M).presheaf.map i.op ≫ (sheaf M).presheaf.germ U p hp) f ∈ I p
  rw [h]
  exact hf p (i.le hp)

end
end FailureOfSemipositiveMetricExtension.Multiplier
