import FailureOfSemipositiveMetricExtension.CoordinateBlowupAdapter.RawCoordinateEquivalence
import FailureOfSemipositiveMetricExtension.CoordinateBlowupOfficial.PreferredIncidenceCentreIdeal
import FailureOfSemipositiveMetricExtension.GlobalIncidenceEquations

/-! The original polynomial family over C[T], not a new unrelated incidence
locus. The accepted equation presentation is identified term by term. -/
namespace FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate.RawAdapter
noncomputable section
open MvPolynomial
universe u
variable (R : Type u) [CommRing R]

open AlgebraicGeometry CategoryTheory in
def schemeIsoOfEquiv {A B : Type u} [CommRing A] [CommRing B] (E : A ≃+* B) :
    Spec (.of A) ≅ Spec (.of B) :=
  (Scheme.Spec.mapIso E.toCommRingCatIso.op).symm

open AlgebraicGeometry CategoryTheory in
theorem schemeIsoOfEquiv_over {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (E : A ≃+* B) (f : C →+* A) (g : C →+* B) (h : ∀ c, E (f c) = g c) :
    (schemeIsoOfEquiv E).hom ≫ Spec.map (CommRingCat.ofHom g) =
      Spec.map (CommRingCat.ofHom f) := by
  change Spec.map (CommRingCat.ofHom E.symm.toRingHom) ≫ _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext c
  change E.symm (g c) = f c
  rw [← h c, RingEquiv.symm_apply_apply]

open AlgebraicGeometry CategoryTheory in
def originalChartSchemeIso (t : R) (a : Fin 3) (e : Fin 4 → Fin 2) :
    Spec (.of (RawFactorRing R t a e)) ≅ Spec (.of (SlopeRing R t a e)) :=
  schemeIsoOfEquiv (originalChartEquiv R t a e).toRingEquiv

/-- Ring-level blowdown triangle; applying Spec contravariantly gives the
corresponding affine-scheme triangle by schemeIsoOfEquiv_over. -/
theorem originalChartEquiv_blowdown (t : R) (a : Fin 3) (e : Fin 4 → Fin 2)
    (f : PairPolynomial R) :
    originalChartEquiv R t a e (baseBack R t a e f) =
      algebraMap (PairPolynomial R) (SlopeRing R t a e) f :=
  DFunLike.congr_fun (forward_baseBack R t a e) f

/-- Pulling back the preferred denominators gives an actual all-prime cover
of the ORIGINAL quotient ring, not merely the slope presentation. -/
def originalPreferredDenominator (t : R) (a : Fin 3) (e : Fin 4 → Fin 2) (r : Fin 4) :
    RawFactorRing R t a e :=
  (originalChartEquiv R t a e).symm (preferredIncidenceDenominator R t a e r)

theorem original_preferred_prime_cover (t : R) (a : Fin 3) (e : Fin 4 → Fin 2)
    (p : PrimeSpectrum (RawFactorRing R t a e)) :
    ∃ r : Fin 4, p ∈ PrimeSpectrum.basicOpen (originalPreferredDenominator R t a e r) := by
  obtain ⟨r,hr⟩ := preferredIncidence_principal_open_cover R t a e
    (PrimeSpectrum.comap (originalChartEquiv R t a e).symm.toRingHom p)
  exact ⟨r,hr⟩

namespace Paper
open FailureOfSemipositiveMetricExtension.GlobalIncidence
open FailureOfSemipositiveMetricExtension.GlobalIncidence.IncidenceEquations

/-- Literally the coefficients and four equations used by the accepted
actual GlobalIncidence presentation over the affine parameter line. -/
theorem rawPair_eq_original (r : Fin 4) (b : Fin 2) :
    rawPair (Polynomial ℂ) Polynomial.X r b = linearPair r b := by
  fin_cases r <;> fin_cases b <;> rfl

theorem rawIncidence_eq_original (r : Fin 4) :
    rawIncidence (Polynomial ℂ) Polynomial.X r = equation r := by
  simp only [rawIncidence, equation, rawPair_eq_original]
  rfl

/-- Normalized factor relations written entirely in the original paper-family
variables and equations. -/
def originalRelations (a : Fin 3) (e : Fin 4 → Fin 2) : Set Equation :=
  ({baseVariable a - 1} ∪ Set.range (fun r => directionVariable r (e r) - 1)) ∪
    Set.range equation

theorem originalRelations_eq (a : Fin 3) (e : Fin 4 → Fin 2) :
    originalRelations a e = rawFactorRelations (Polynomial ℂ) Polynomial.X a e := by
  unfold originalRelations rawFactorRelations
  rw [show rawIncidence (Polynomial ℂ) Polynomial.X = equation from
    funext rawIncidence_eq_original]
  rfl

abbrev OriginalChartRing (a : Fin 3) (e : Fin 4 → Fin 2) :=
  Equation ⧸ Ideal.span (originalRelations a e)

/-- This exact ring isomorphism applies to the quotient of the original
C[T]-polynomials, with the original parameter and all blowdown coordinates. -/
def actualOriginalChartEquiv (a : Fin 3) (e : Fin 4 → Fin 2) :
    OriginalChartRing a e ≃ₐ[Polynomial ℂ]
      SlopeRing (Polynomial ℂ) Polynomial.X a e := by
  unfold OriginalChartRing
  rw [originalRelations_eq]
  exact originalChartEquiv (Polynomial ℂ) Polynomial.X a e

/-- The equations used for that unreduced ring define exactly the accepted
actual complex incidence locus on every set of nonzero representatives. -/
theorem actual_total_iff_original_raw_equations (t : ℂ) (v : Fin 3 → ℂ) (hv : v ≠ 0)
    (w : Fin 4 → Fin 2 → ℂ) (hw : ∀ r, w r ≠ 0) :
    (Projectivization.mk ℂ v hv,(fun r => Projectivization.mk ℂ (w r) (hw r)),t) ∈ totalLocus ↔
      ∀ r, evaluate t v w (rawIncidence (Polynomial ℂ) Polynomial.X r) = 0 := by
  simp only [rawIncidence_eq_original]
  exact totalLocus_iff_equations t v hv w hw

end Paper
end
end FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate.RawAdapter
