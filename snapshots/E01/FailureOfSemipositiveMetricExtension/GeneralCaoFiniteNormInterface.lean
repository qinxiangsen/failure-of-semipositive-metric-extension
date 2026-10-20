import FailureOfSemipositiveMetricExtension.GeneralCanonicalNormMeasurability

/-! Review-only general Cao input with an actual finite canonical-norm cover.
Unlike the previously specialized literature input, no projective immersion,
threefold dimension, global submersion, or base shrinking is imposed.
No literature axiom is declared here. -/
namespace FailureOfSemipositiveMetricExtension.GeneralCao
noncomputable section
open Set Topology MeasureTheory
open scoped Manifold ContDiff

variable {n : ℕ} {M N : Type} [TopologicalSpace M] [ChartedSpace (Coord (n+1)) M]
    [TopologicalSpace N] [ChartedSpace (Coord n) N]
    [T2Space M] [SecondCountableTopology M] [IsManifold 𝓘(ℂ,Coord (n+1)) ω M]
    [T2Space N] [SecondCountableTopology N] [IsManifold 𝓘(ℂ,Coord n) ω N]
    {A B J : Type} (G : Family n M N A B) (L : AnalyticLine n (M := M) J)

/-- Generic literature interface candidate: proper over the unit OPEN disc,
a genuine Kähler form, a genuine semipositive line weight, a well-defined central
restriction, and a finite cover by true canonical norm patches. The extension is
on the WHOLE total manifold and uses normal-LAST adjunction. -/
def FiniteNormExtensionStatement : Prop :=
  ∀ (_kahler : GeneralKahler.KahlerForm G.totalAtlas)
    (h : SemipositiveWeight n G L), RestrictionWellDefined n G L h →
    ∀ s : CentralAdjointSection n G L, Nonempty (CanonicalNormFiniteCover G L s h) →
      ∃ S : TotalAdjointSection n G L, RestrictsByDt n G L S s

/-- The whole local-to-global L2 step is proved, rather than absorbed into the
literature interface: actual stalk hypotheses yield the required finite cover. -/
theorem extensionStatement_of_finiteNorm [CompactSpace N]
    (H : FiniteNormExtensionStatement G L) : ExtensionStatement n G L := by
  letI : MeasurableSpace N := borel N
  letI : BorelSpace N := ⟨rfl⟩
  intro η h hw s hs
  exact H η h hw s (canonicalNormFiniteCover_nonempty G L s h hs)

/-- Central compactness is also derived from the actual proper map to the disc. -/
theorem multiplier_extension_of_finiteNorm
    (H : FiniteNormExtensionStatement G L) (η : GeneralKahler.KahlerForm G.totalAtlas)
    (h : SemipositiveWeight n G L) (hw : RestrictionWellDefined n G L h)
    (s : CentralAdjointSection n G L) (hs : InRestrictedMultiplier n G L h s) :
    ∃ S : TotalAdjointSection n G L, RestrictsByDt n G L S s := by
  letI : MeasurableSpace N := borel N
  letI : BorelSpace N := ⟨rfl⟩
  letI : CompactSpace N := G.central_compact n
  exact H η h hw s (canonicalNormFiniteCover_nonempty G L s h hs)

end
end FailureOfSemipositiveMetricExtension.GeneralCao
