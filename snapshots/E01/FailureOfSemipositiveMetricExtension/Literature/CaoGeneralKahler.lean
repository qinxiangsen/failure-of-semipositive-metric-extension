import FailureOfSemipositiveMetricExtension.GeneralCaoFiniteNormInterface

/-! DISCLOSED SIXTH LITERATURE INPUT, approved for the paper's explicit
pre-existing-literature exception. This is a generic full-dimensional
existence-only translation of Cao, arXiv:1404.6937v2, Theorem 1.1 p.1,
Remark 3 p.3 and Corollary 3.1 p.9. The actual local-to-global finite norm
bridge is proved separately. Trusted translations include the actual Kähler
form/bundle language and psh weights to positive currents plus a smooth
reference metric. There is no projective-immersion input and no claimed
optimal estimate. Unit-disc and normal-last conventions are explicit.
See docs/stage9_general_cao_interface_review.md. -/
namespace FailureOfSemipositiveMetricExtension.Literature
open scoped Manifold ContDiff

axiom cao_extension_proper_disc_kahler_psh_translation
    {n : ℕ} {M N : Type}
    [TopologicalSpace M] [ChartedSpace (GeneralCao.Coord (n+1)) M]
    [T2Space M] [SecondCountableTopology M] [IsManifold 𝓘(ℂ,GeneralCao.Coord (n+1)) ω M]
    [TopologicalSpace N] [ChartedSpace (GeneralCao.Coord n) N]
    [T2Space N] [SecondCountableTopology N] [IsManifold 𝓘(ℂ,GeneralCao.Coord n) ω N]
    {A B J : Type} (G : GeneralCao.Family n M N A B) (L : GeneralCao.AnalyticLine n (M := M) J) :
    GeneralCao.FiniteNormExtensionStatement G L

end FailureOfSemipositiveMetricExtension.Literature
