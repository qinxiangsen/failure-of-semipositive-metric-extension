import FailureOfSemipositiveMetricExtension.GeneralTensorPowerWeights
import FailureOfSemipositiveMetricExtension.GeneralGermWeightCongruence
import FailureOfSemipositiveMetricExtension.GeneralAdjunctionAlgebra
import FailureOfSemipositiveMetricExtension.Literature.CaoGeneralKahler

/-! The full-dimensional adjoint-obstruction proposition and its all-positive-
integer tensor-power consequence, with genuine global extension and dt.
Only the separately disclosed generic Cao translation is an external input. -/
namespace FailureOfSemipositiveMetricExtension.GeneralCao
noncomputable section
open Set Topology
open scoped Manifold ContDiff

variable {n : ℕ} {M N : Type}
    [TopologicalSpace M] [ChartedSpace (Coord (n+1)) M]
    [T2Space M] [SecondCountableTopology M] [IsManifold 𝓘(ℂ,Coord (n+1)) ω M]
    [TopologicalSpace N] [ChartedSpace (Coord n) N]
    [T2Space N] [SecondCountableTopology N] [IsManifold 𝓘(ℂ,Coord n) ω N]
    {A B J : Type} (G : Family n M N A B) (L : AnalyticLine n (M := M) J)

theorem adjoint_obstruction (η : GeneralKahler.KahlerForm G.totalAtlas)
    (h : SemipositiveWeight n G L) (hw : RestrictionWellDefined n G L h)
    (s : CentralAdjointSection n G L) (hs : InRestrictedMultiplier n G L h s) :
    ∃ S : TotalAdjointSection n G L, RestrictsByDt n G L S s :=
  multiplier_extension_of_finiteNorm G L
    (Literature.cao_extension_proper_disc_kahler_psh_translation G L) η h hw s hs

theorem adjoint_obstruction_all_positive_powers (η : GeneralKahler.KahlerForm G.totalAtlas)
    (h : SemipositiveWeight n G L) (hw : RestrictionWellDefined n G L h)
    (m : ℕ) (hm : 0 < m) (s : CentralAdjointSection n G (L.powerLine m))
    (hs : InPowerRestrictedMultiplier G L h m s) :
    ∃ S : TotalAdjointSection n G (L.powerLine m), RestrictsByDt n G (L.powerLine m) S s :=
  adjoint_obstruction G (L.powerLine m) η (h.power G L m hm) (h.power_wellDefined G L hw m hm) s
    ((power_restrictedMultiplier_iff G L h m hm s).mpr hs)

/-- Integrable actual central adjoint section for an independently prescribed
central metric weight, with no conditions on its arbitrary off-frame values. -/
def PrescribedCentralPowerMultiplier (w₀ : J → N → WithBot ℝ) (m : ℕ)
    (s : CentralAdjointSection n G (L.powerLine m)) : Prop :=
  ∀ (a : A) (i : J) (p : N) (hp : p ∈ centralPatch n G (L.powerLine m) a i),
    GeneralMultiplier.IntegrableGerm n N m (w₀ i) p
      ((GeneralMultiplier.sheaf n N).presheaf.germ (centralPatch n G (L.powerLine m) a i) p hp
        (centralCoefficientSection n G (L.powerLine m) s a i))

/-- Exactly the consequence in the paper: a metric extension of the
prescribed central metric forces extension for EVERY positive tensor power. -/
theorem prescribed_metric_adjoint_extension_all_m (η : GeneralKahler.KahlerForm G.totalAtlas)
    (w₀ : J → N → WithBot ℝ)
    (hw₀ : ∀ p : N, ∃ q ∈ connectedComponent p, ∃ i : J,
      G.inclusion q ∈ L.core.baseSet i ∧ w₀ i q ≠ ⊥)
    (h : SemipositiveWeight n G L)
    (hrestrict : ∀ i p, G.inclusion p ∈ L.core.baseSet i → h.weight i (G.inclusion p) = w₀ i p)
    (m : ℕ) (hm : 0 < m) (s : CentralAdjointSection n G (L.powerLine m))
    (hs : PrescribedCentralPowerMultiplier G L w₀ m s) :
    ∃ S : TotalAdjointSection n G (L.powerLine m), RestrictsByDt n G (L.powerLine m) S s := by
  have hw : RestrictionWellDefined n G L h := by
    intro p
    obtain ⟨q,hq,i,hi,hfinite⟩ := hw₀ p
    exact ⟨q,hq,i,hi,by rwa [hrestrict i q hi]⟩
  apply adjoint_obstruction_all_positive_powers G L η h hw m hm s
  intro a i p hp
  apply (GeneralMultiplier.integrableGerm_section_congr_weight n N m
    (fun q => h.weight i (G.inclusion q)) (w₀ i)
    (centralPatch n G (L.powerLine m) a i) (centralCoefficientSection n G (L.powerLine m) s a i)
    p hp (fun q hq => hrestrict i q hq.2)).mpr
  exact hs a i p hp

end
end FailureOfSemipositiveMetricExtension.GeneralCao
