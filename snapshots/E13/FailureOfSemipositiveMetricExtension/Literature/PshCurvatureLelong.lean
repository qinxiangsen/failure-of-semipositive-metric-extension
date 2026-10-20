import FailureOfSemipositiveMetricExtension.PshCurvatureCurrentInterface

/-!
EXTERNAL COMPOSITE STANDARD COROLLARY, stage 8.
Demailly, Analytic Methods in Algebraic Geometry, 1.5(a), Theorem 1.7,
1.12–1.16, and Theorem 2.8, printed pp.7–10 and 17–18.

The precise trust boundary is recorded in
`docs/stage8_psh_current_interface_review.md`: local L1 and finite-a.e. psh
representatives; computed real Hessian polarization as complex distribution
coefficients; their order-two topology, positivity and closedness; the positive
trace measure and its normalization; and the Lelong mass/growth theorem,
including Euclidean versus maximum-product norm equivalence.

The actual derivatives, tests, matrix coefficients, weak trace, trace measure,
Euclidean balls and mass limit are defined in the imported interface. This
universal fact has no paper-specific family, metric, divisor or numerical Lelong
value. It does not implement global-current coordinate gluing.
-/
namespace FailureOfSemipositiveMetricExtension.Literature

axiom psh_curvature_current_lelong_via_distribution_translation :
  PshCurvatureCurrentInterface.PshCurrentStatement

end FailureOfSemipositiveMetricExtension.Literature
