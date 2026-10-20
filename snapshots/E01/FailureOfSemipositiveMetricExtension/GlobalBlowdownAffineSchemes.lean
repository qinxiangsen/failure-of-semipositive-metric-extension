import FailureOfSemipositiveMetricExtension.GlobalBlowdownLocalizedAlgebra
import Mathlib.AlgebraicGeometry.AffineScheme

/-! The proved localized incidence-ring isomorphism induces an actual isomorphism
of mathlib schemes onto a dense principal open of affine three-space. These are
local scheme charts; no identification with a global multi-projective scheme is
assumed or claimed here. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.BlowdownComplement
noncomputable section
open CategoryTheory AlgebraicGeometry

abbrev affineBaseScheme : Scheme := Spec (CommRingCat.of AffinePolynomial)

abbrev localizedBaseScheme (a : Fin 3) (e : Fin 4 → Fin 2) : Scheme :=
  Spec (CommRingCat.of (ChartRing a e))

abbrev localizedIncidenceScheme (a : Fin 3) (e : Fin 4 → Fin 2) : Scheme :=
  Spec (CommRingCat.of (GraphPolynomial a e ⧸ incidenceChartIdeal a e))

/-- This is an isomorphism of actual locally ringed spaces, not only their spectra. -/
def localizedIncidenceIso (a : Fin 3) (e : Fin 4 → Fin 2) :
    localizedIncidenceScheme a e ≅ localizedBaseScheme a e :=
  (Scheme.Spec.mapIso (incidenceChartRingEquiv a e).toCommRingCatIso.op).symm

/-- The actual dense principal open subscheme of affine three-space. -/
def baseOpen (a : Fin 3) (e : Fin 4 → Fin 2) : affineBaseScheme.Opens := zariskiChart a e

def localizationMap (a : Fin 3) (e : Fin 4 → Fin 2) :
    localizedBaseScheme a e ⟶ affineBaseScheme :=
  Spec.map (CommRingCat.ofHom (algebraMap AffinePolynomial (ChartRing a e)))

instance localizationMap_isOpenImmersion (a : Fin 3) (e : Fin 4 → Fin 2) :
    IsOpenImmersion (localizationMap a e) := by
  unfold localizationMap
  exact IsOpenImmersion.of_isLocalization (chartDenominator a e)

theorem range_localizationMap (a : Fin 3) (e : Fin 4 → Fin 2) :
    Set.range (localizationMap a e).base = (baseOpen a e : Set affineBaseScheme) :=
  PrimeSpectrum.localization_away_comap_range (ChartRing a e) (chartDenominator a e)

def localizedBaseOpenIso (a : Fin 3) (e : Fin 4 → Fin 2) :
    localizedBaseScheme a e ≅ (baseOpen a e).toScheme :=
  IsOpenImmersion.isoOfRangeEq (localizationMap a e) (baseOpen a e).ι (by
    rw [range_localizationMap]
    exact (baseOpen a e).range_ι.symm)

/-- The localized original incidence equations define a scheme genuinely
isomorphic to this dense Zariski open. -/
def localizedIncidenceOpenIso (a : Fin 3) (e : Fin 4 → Fin 2) :
    localizedIncidenceScheme a e ≅ (baseOpen a e).toScheme :=
  (localizedIncidenceIso a e) ≪≫ (localizedBaseOpenIso a e)

theorem baseOpen_dense (a : Fin 3) (e : Fin 4 → Fin 2) :
    Dense (baseOpen a e : Set affineBaseScheme) := zariskiChart_dense a e

/-- The inverse algebraic chart composed with inclusion is the original
localization map, fixing the direction of the scheme isomorphism. -/
theorem localizedBaseOpenIso_hom_inclusion (a : Fin 3) (e : Fin 4 → Fin 2) :
    (localizedBaseOpenIso a e).hom ≫ (baseOpen a e).ι = localizationMap a e :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.BlowdownComplement
