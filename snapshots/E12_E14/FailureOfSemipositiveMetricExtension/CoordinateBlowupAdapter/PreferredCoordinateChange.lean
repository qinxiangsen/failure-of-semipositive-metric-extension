import FailureOfSemipositiveMetricExtension.CoordinateBlowupOfficial.PreferredCentreAffineCover

/-! Explicit coordinates for each of the paper's four moving centres in its
preferred affine plane. These are polynomial automorphisms over ANY parameter
coefficient ring, hence also over C[T]. -/
namespace FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate.RawAdapter
noncomputable section
open MvPolynomial
universe u
variable (R : Type u) [CommRing R]

def centreOffset (t : R) (r : Fin 4) (b : Fin 2) : R :=
  if r = 2 then if b = 0 then 1 else t else 0

theorem preferredPair_explicit (t : R) (r : Fin 4) (b : Fin 2) :
    normalizedPair R t (preferredCentreChart r) r b = X b - C (centreOffset R t r b) := by
  fin_cases r <;> fin_cases b <;>
    simp [normalizedPair, normalizedVector, preferredCentreChart, centreOffset]

def shiftToCentre (t : R) (r : Fin 4) : PairPolynomial R →ₐ[R] PairPolynomial R :=
  aeval fun b => X b - C (centreOffset R t r b)

def shiftFromCentre (t : R) (r : Fin 4) : PairPolynomial R →ₐ[R] PairPolynomial R :=
  aeval fun b => X b + C (centreOffset R t r b)

theorem shiftToFrom (t : R) (r : Fin 4) :
    (shiftToCentre R t r).comp (shiftFromCentre R t r) = AlgHom.id R _ := by
  ext b
  simp [shiftToCentre, shiftFromCentre]

theorem shiftFromTo (t : R) (r : Fin 4) :
    (shiftFromCentre R t r).comp (shiftToCentre R t r) = AlgHom.id R _ := by
  ext b
  simp [shiftToCentre, shiftFromCentre]

/-- The retained centre equations ARE coordinate variables after this explicit
polynomial change. The family coefficient (in particular T) is unchanged. -/
def preferredCoordinateEquiv (t : R) (r : Fin 4) :
    PairPolynomial R ≃ₐ[R] PairPolynomial R :=
  AlgEquiv.ofAlgHom (shiftToCentre R t r) (shiftFromCentre R t r)
    (shiftToFrom R t r) (shiftFromTo R t r)

@[simp] theorem preferredCoordinateEquiv_X (t : R) (r : Fin 4) (b : Fin 2) :
    preferredCoordinateEquiv R t r (X b) =
      normalizedPair R t (preferredCentreChart r) r b := by
  rw [preferredPair_explicit]
  exact aeval_X _ b

@[simp] theorem preferredCoordinateEquiv_symm_pair (t : R) (r : Fin 4) (b : Fin 2) :
    (preferredCoordinateEquiv R t r).symm
      (normalizedPair R t (preferredCentreChart r) r b) = X b := by
  rw [← preferredCoordinateEquiv_X R t r b, AlgEquiv.symm_apply_apply]

theorem preferredCoordinateEquiv_centre_ideal (t : R) (r : Fin 4) :
    (pairIdeal (X 0 : PairPolynomial R) (X 1)).map
      (preferredCoordinateEquiv R t r).toRingHom =
      normalizedCentreIdeal R t (preferredCentreChart r) r := by
  rw [pairIdeal, Ideal.map_span, Set.image_pair]
  change Ideal.span {preferredCoordinateEquiv R t r (X 0),
    preferredCoordinateEquiv R t r (X 1)} = _
  rw [preferredCoordinateEquiv_X, preferredCoordinateEquiv_X]
  rfl

end
end FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate.RawAdapter
