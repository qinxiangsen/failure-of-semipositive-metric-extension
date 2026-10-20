import FailureOfSemipositiveMetricExtension.Plurisubharmonic

/-! EXTERNAL LITERATURE THEOREM, not a proved project theorem.
Demailly, Analytic Methods in Algebraic Geometry, Definition 1.4 and properties
1.5(d), Example 1.9 (pp.6--8), and Example 3.14 (pp.26--27).
Primary source: https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/analmeth_book.pdf
Positive multiples of the logarithm of a sum of squared moduli of holomorphic
functions are psh, including their common-zero locus. The definition here uses
all lower-truncated circular means for the extended integral.
No specific surface, section, bundle, or conclusion of the uploaded paper occurs. -/
namespace FailureOfSemipositiveMetricExtension.Literature
open Set
open scoped ContDiff

axiom log_sum_squares_plurisubharmonic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {m : ℕ} (f : Fin m → E → ℂ) (U : Set E) (hU : IsOpen U)
    (hf : ∀ k, ContDiffOn ℂ ω (f k) U) (c : ℝ) (hc : 0 < c) :
    FailureOfSemipositiveMetricExtension.PlurisubharmonicOn (FailureOfSemipositiveMetricExtension.logSumSquaresWeight c f) U

end FailureOfSemipositiveMetricExtension.Literature
