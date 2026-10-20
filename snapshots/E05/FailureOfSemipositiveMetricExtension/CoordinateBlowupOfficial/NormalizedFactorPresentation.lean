import FailureOfSemipositiveMetricExtension.CoordinateBlowupOfficial.EliminateOtherDirections

/-! Exact normalization of the four original bilinear incidence equations.
The base and each direction pivot are set to one in the original polynomial
quotient; the result is a four-slope equation quotient over affine two-space.
No radical or reduced quotient is introduced. -/
namespace FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate
noncomputable section
open MvPolynomial
universe u
variable (R : Type u) [CommRing R]

abbrev RawFactorPolynomial := MvPolynomial (Fin 3 ⊕ (Fin 4 × Fin 2)) R
abbrev SlopePolynomial := MvPolynomial (Fin 4) (PairPolynomial R)

def rawBase (a : Fin 3) : RawFactorPolynomial R := X (Sum.inl a)
def rawDirection (r : Fin 4) (e : Fin 2) : RawFactorPolynomial R := X (Sum.inr (r,e))

def rawPair (t : R) : Fin 4 → Fin 2 → RawFactorPolynomial R
  | 0 => ![rawBase R 1, rawBase R 2]
  | 1 => ![rawBase R 0, rawBase R 2]
  | 2 => ![rawBase R 1 - rawBase R 0, rawBase R 2 - C t * rawBase R 0]
  | 3 => ![rawBase R 0, rawBase R 1]

def rawIncidence (t : R) (r : Fin 4) : RawFactorPolynomial R :=
  rawPair R t r 0 * rawDirection R r 1 - rawPair R t r 1 * rawDirection R r 0

def rawFactorRelations (t : R) (a : Fin 3) (e : Fin 4 → Fin 2) : Set (RawFactorPolynomial R) :=
  ({rawBase R a - 1} ∪ Set.range (fun r => rawDirection R r (e r) - 1)) ∪
    Set.range (rawIncidence R t)

def rawFactorIdeal (t : R) (a : Fin 3) (e : Fin 4 → Fin 2) : Ideal (RawFactorPolynomial R) :=
  Ideal.span (rawFactorRelations R t a e)

abbrev RawFactorRing (t : R) (a : Fin 3) (e : Fin 4 → Fin 2) :=
  RawFactorPolynomial R ⧸ rawFactorIdeal R t a e

def slopeRelation (t : R) (a : Fin 3) (e : Fin 4 → Fin 2) (r : Fin 4) : SlopePolynomial R :=
  C (normalizedPair R t a r (e r)) * X r - C (normalizedPair R t a r (e r).rev)

def slopeIdeal (t : R) (a : Fin 3) (e : Fin 4 → Fin 2) : Ideal (SlopePolynomial R) :=
  Ideal.span (Set.range (slopeRelation R t a e))

abbrev SlopeRing (t : R) (a : Fin 3) (e : Fin 4 → Fin 2) :=
  SlopePolynomial R ⧸ slopeIdeal R t a e

def normalizedRawDirection (t : R) (a : Fin 3) (e : Fin 4 → Fin 2)
    (r : Fin 4) (b : Fin 2) : SlopeRing R t a e :=
  if b = e r then 1 else Ideal.Quotient.mk _ (X r)

def rawNormalization (t : R) (a : Fin 3) (e : Fin 4 → Fin 2) :
    RawFactorPolynomial R →ₐ[R] SlopeRing R t a e :=
  aeval fun i => match i with
    | Sum.inl b => algebraMap (PairPolynomial R) (SlopeRing R t a e) (normalizedVector R a b)
    | Sum.inr (r,b) => normalizedRawDirection R t a e r b

@[simp] theorem rawNormalization_base (t : R) (a b : Fin 3) (e : Fin 4 → Fin 2) :
    rawNormalization R t a e (rawBase R b) =
      algebraMap (PairPolynomial R) (SlopeRing R t a e) (normalizedVector R a b) := by
  simp [rawNormalization, rawBase]

@[simp] theorem rawNormalization_direction (t : R) (a : Fin 3) (e : Fin 4 → Fin 2)
    (r : Fin 4) (b : Fin 2) :
    rawNormalization R t a e (rawDirection R r b) = normalizedRawDirection R t a e r b := by
  simp [rawNormalization, rawDirection]

@[simp] theorem normalizedRawDirection_selected (t : R) (a : Fin 3)
    (e : Fin 4 → Fin 2) (r : Fin 4) : normalizedRawDirection R t a e r (e r) = 1 := by
  simp [normalizedRawDirection]

@[simp] theorem normalizedRawDirection_other (t : R) (a : Fin 3)
    (e : Fin 4 → Fin 2) (r : Fin 4) :
    normalizedRawDirection R t a e r (e r).rev = Ideal.Quotient.mk _ (X r) := by
  have h : (e r).rev ≠ e r := by generalize e r = b; fin_cases b <;> decide
  simp [normalizedRawDirection, h]

theorem rawNormalization_pair (t : R) (a : Fin 3) (e : Fin 4 → Fin 2)
    (r : Fin 4) (b : Fin 2) :
    rawNormalization R t a e (rawPair R t r b) =
      algebraMap (PairPolynomial R) (SlopeRing R t a e) (normalizedPair R t a r b) := by
  fin_cases r <;> fin_cases b <;>
    simp [rawPair, normalizedPair, rawNormalization_base, map_sub, map_mul]
  rfl

theorem slope_relation_zero (t : R) (a : Fin 3) (e : Fin 4 → Fin 2) (r : Fin 4) :
    Ideal.Quotient.mk (slopeIdeal R t a e) (slopeRelation R t a e r) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨r,rfl⟩)

theorem rawNormalization_incidence (t : R) (a : Fin 3) (e : Fin 4 → Fin 2) (r : Fin 4) :
    rawNormalization R t a e (rawIncidence R t r) = 0 := by
  have hrel : algebraMap (PairPolynomial R) (SlopeRing R t a e) (normalizedPair R t a r (e r)) *
      Ideal.Quotient.mk _ (X r) =
        algebraMap (PairPolynomial R) (SlopeRing R t a e) (normalizedPair R t a r (e r).rev) :=
    by
      apply sub_eq_zero.mp
      change Ideal.Quotient.mk (slopeIdeal R t a e) (slopeRelation R t a e r) = 0
      exact slope_relation_zero R t a e r
  simp only [rawIncidence, map_sub, map_mul, rawNormalization_pair, rawNormalization_direction]
  generalize he : e r = b at hrel ⊢
  fin_cases b
  · simpa [normalizedRawDirection, he] using sub_eq_zero.mpr hrel
  · simpa [normalizedRawDirection, he] using sub_eq_zero.mpr hrel.symm

theorem rawNormalization_relations (t : R) (a : Fin 3) (e : Fin 4 → Fin 2)
    (f : RawFactorPolynomial R) (hf : f ∈ rawFactorRelations R t a e) :
    rawNormalization R t a e f = 0 := by
  rcases hf with (rfl | ⟨r,rfl⟩) | ⟨r,rfl⟩
  · simp only [map_sub, rawNormalization_base, map_one]
    have h : normalizedVector R a a = 1 := by fin_cases a <;> rfl
    rw [h, map_one, sub_self]
  · simp
  · exact rawNormalization_incidence R t a e r

def rawToSlope (t : R) (a : Fin 3) (e : Fin 4 → Fin 2) :
    RawFactorRing R t a e →ₐ[R] SlopeRing R t a e :=
  Ideal.Quotient.liftₐ _ (rawNormalization R t a e) (by
    have h : rawFactorIdeal R t a e ≤ RingHom.ker (rawNormalization R t a e).toRingHom :=
      Ideal.span_le.mpr (fun f hf => rawNormalization_relations R t a e f hf)
    exact fun f hf => h hf)

end
end FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate
