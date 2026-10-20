import FailureOfSemipositiveMetricExtension.CaoExtensionInterface

/-!
EXTERNAL LITERATURE COROLLARY, WITH EXPLICIT COMPOSITE TRUST BOUNDARY.

Cao, arXiv:1404.6937v2, Theorem 1.1 p.1, existence part, together with:
(1) Fubini--Study and Euclidean Kähler forms and their holomorphic immersion
    pullback (Demailly, Analytic Methods, Example 3.14 and §3.15, pp.26--27);
(2) compatible psh weights define positive-curvature singular Hermitian metrics,
    and a smooth reference metric exists on a paracompact complex manifold
    (Demailly §3.10--3.12, pp.25--26);
(3) the standard chart/germ formulation of multiplier membership, and proper
    restriction to a disc after shrinking an entire central-fibre neighbourhood.

These generic translations are trusted with Cao; they are NOT claimed to have
been constructed as differential forms, currents or partitions of unity in Lean.
The exact universal proposition and all actual-object types are defined in the
imported interface. No fact about this paper's family or distinguished section
is an input to justify this external theorem. Actual applicability is separate.
-/
namespace FailureOfSemipositiveMetricExtension.Literature
noncomputable section
open FailureOfSemipositiveMetricExtension.CaoExtensionInterface
open scoped Manifold ContDiff

axiom cao_extension_via_projective_immersion_psh_translation
    {M N : Type} [TopologicalSpace M] [ChartedSpace TotalCoord M]
    [T2Space M] [SecondCountableTopology M] [IsManifold 𝓘(ℂ,TotalCoord) ω M]
    [TopologicalSpace N] [ChartedSpace SurfaceCoord N]
    [T2Space N] [SecondCountableTopology N] [CompactSpace N]
    [IsManifold 𝓘(ℂ,SurfaceCoord) ω N]
    {A J : Type} (G : AdaptedFamily M N A) (L : AnalyticLineBundle (M := M) J) :
    ExtensionStatement G L

end
end FailureOfSemipositiveMetricExtension.Literature
