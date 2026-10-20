import FailureOfSemipositiveMetricExtension.CurrentCoordinateCovariance

/-! EXTERNAL COMPOSITE STANDARD LOCAL DISTRIBUTION-CALCULUS FACT.
Demailly, Analytic Methods in Algebraic Geometry, §1.C pp9–10, equation 1.20
pp11–12, and 3.10–3.12 pp25–26. This is a precisely typed consequence, not a
verbatim numbered theorem. The weak derivative chain rule, test-density change
of variables with the genuine inverse Jacobian, complex test extension, compact
zero extension and holomorphic gauge invariance are trusted as documented in
stage10_current_covariance_interface_review.md. No paper-specific current,
Lelong value, gluing result or cohomology assertion is an input. -/
namespace FailureOfSemipositiveMetricExtension.Literature

axiom distributional_ddc_coordinate_gauge_covariance :
  CurrentCoordinateCovariance.CovarianceStatement

end FailureOfSemipositiveMetricExtension.Literature
