import FailureOfSemipositiveMetricExtension.PoincareLelongIntegrationInterface

/-! Explicitly approved universal integration-current/Poincare--Lelong fact.
Demailly (1.17) p10 and (1.20) p12. The actual curve-parameter area integral,
one omitted P1 point of zero area, full current descent and multiplicity-one
normalization translations are trusted as individually documented in
stage11_poincare_lelong_interface_review.md. No paper-specific conclusion. -/
namespace FailureOfSemipositiveMetricExtension.Literature
axiom smooth_rational_divisor_poincare_lelong_integration_translation :
  PoincareLelongIntegrationInterface.IntegrationStatement
end FailureOfSemipositiveMetricExtension.Literature
