import FailureOfSemipositiveMetricExtension.NegativeCurveRemovalInterface

/-!
EXTERNAL COMPOSITE LITERATURE COROLLARY (stage 8, separate from frozen stage 7).

Boucksom, Ann. Sci. ENS 37 (2004), Theorems 4.5 and 4.8, pp.64–65;
§3.1 after Definition 3.1, p.54; Siu decomposition §2.2.1, p.48.
Together with the EXPLICIT standard translations reviewed in
negative_curve_removal_interface_review.md:
- projective immersion gives Kähler; globally generated gives nef, without bigness;
- actual simple divisor / Cech tensor / standard P¹ pullback degrees give the
  Chern and intersection identities;
- compatible psh weights give currents; divisorial removal gives the unique psh
  representative off the divisor, glues in the true B frames, and has the exact
  extended-value identity on the divisor because h is minus infinity there;
- identically minus-infinity connected components are treated separately, and
  components avoiding the divisor subtract a nonvanishing pluriharmonic log.

This generic corollary is not a verbatim single theorem and does NOT construct
currents or their classes in Lean. It mentions no paper-specific surface,
line bundle, exponent, metric or claimed minimality conclusion.
-/
namespace FailureOfSemipositiveMetricExtension.Literature
noncomputable section
open FailureOfSemipositiveMetricExtension.NegativeCurveRemovalInterface
open scoped Manifold ContDiff

axiom negative_curve_psh_removal_via_zariski_siu_translation
    {M : Type} [TopologicalSpace M] [ChartedSpace Coord M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [IsManifold 𝓘(ℂ,Coord) ω M] {A J : Type}
    (atlas : CaoExtensionInterface.AnalyticAtlas Coord M A)
    (L B D : AnalyticLine M J) : RemovalStatement atlas L B D

end
end FailureOfSemipositiveMetricExtension.Literature
