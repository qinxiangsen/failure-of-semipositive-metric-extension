import FailureOfSemipositiveMetricExtension.CoordinateBlowupOfficial.NormalizedFactorPresentation

/-! A bounded, independent inverse-coordinate adapter for the original
unreduced projective-factor quotient. No radical is taken. -/
namespace FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate.RawAdapter
noncomputable section
open MvPolynomial
universe u
variable (R : Type u) [CommRing R]

def freeIndex : Fin 3 → Fin 2 → Fin 3
  | 0 => ![1,2]
  | 1 => ![0,2]
  | 2 => ![0,1]

def baseBack (t : R) (a : Fin 3) (e : Fin 4 → Fin 2) :
    PairPolynomial R →ₐ[R] RawFactorRing R t a e :=
  aeval fun j => Ideal.Quotient.mk _ (rawBase R (freeIndex a j))

theorem raw_base_pivot (t : R) (a : Fin 3) (e : Fin 4 → Fin 2) :
    Ideal.Quotient.mk (rawFactorIdeal R t a e) (rawBase R a) = 1 := by
  apply sub_eq_zero.mp
  change Ideal.Quotient.mk (rawFactorIdeal R t a e) (rawBase R a - 1) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (Or.inl (Or.inl rfl))

theorem raw_direction_pivot (t : R) (a : Fin 3) (e : Fin 4 → Fin 2) (r : Fin 4) :
    Ideal.Quotient.mk (rawFactorIdeal R t a e) (rawDirection R r (e r)) = 1 := by
  apply sub_eq_zero.mp
  change Ideal.Quotient.mk (rawFactorIdeal R t a e) (rawDirection R r (e r) - 1) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (Or.inl (Or.inr ⟨r,rfl⟩))

theorem baseBack_vector (t : R) (a b : Fin 3) (e : Fin 4 → Fin 2) :
    baseBack R t a e (normalizedVector R a b) =
      Ideal.Quotient.mk (rawFactorIdeal R t a e) (rawBase R b) := by
  have h := raw_base_pivot R t a e
  fin_cases a <;> fin_cases b <;>
    simp [baseBack, normalizedVector, freeIndex]
  all_goals exact h.symm

theorem baseBack_pair (t : R) (a : Fin 3) (e : Fin 4 → Fin 2)
    (r : Fin 4) (b : Fin 2) :
    baseBack R t a e (normalizedPair R t a r b) =
      Ideal.Quotient.mk (rawFactorIdeal R t a e) (rawPair R t r b) := by
  fin_cases r <;> fin_cases b <;>
    simp [normalizedPair, rawPair, baseBack_vector, map_sub, map_mul]
  rfl

def slopeBackEval (t : R) (a : Fin 3) (e : Fin 4 → Fin 2) :
    SlopePolynomial R →ₐ[R] RawFactorRing R t a e :=
  aevalTower (baseBack R t a e)
    (fun r => Ideal.Quotient.mk _ (rawDirection R r (e r).rev))

@[simp] theorem slopeBackEval_C (t : R) (a : Fin 3) (e : Fin 4 → Fin 2)
    (f : PairPolynomial R) : slopeBackEval R t a e (C f) = baseBack R t a e f := by
  simp [slopeBackEval]

@[simp] theorem slopeBackEval_X (t : R) (a : Fin 3) (e : Fin 4 → Fin 2)
    (r : Fin 4) : slopeBackEval R t a e (X r) =
      Ideal.Quotient.mk _ (rawDirection R r (e r).rev) := by
  simp [slopeBackEval]

theorem raw_incidence_zero (t : R) (a : Fin 3) (e : Fin 4 → Fin 2) (r : Fin 4) :
    Ideal.Quotient.mk (rawFactorIdeal R t a e) (rawIncidence R t r) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Or.inr ⟨r,rfl⟩))

theorem slopeBackEval_relation (t : R) (a : Fin 3) (e : Fin 4 → Fin 2) (r : Fin 4) :
    slopeBackEval R t a e (slopeRelation R t a e r) = 0 := by
  have h := raw_incidence_zero R t a e r
  have hp := raw_direction_pivot R t a e r
  simp only [slopeRelation, map_sub, map_mul, slopeBackEval_C, slopeBackEval_X, baseBack_pair]
  simp only [rawIncidence, map_sub, map_mul] at h
  generalize he : e r = b at hp ⊢
  fin_cases b
  · change Ideal.Quotient.mk (rawFactorIdeal R t a e) (rawDirection R r 0) = 1 at hp
    simpa [hp] using h
  · change Ideal.Quotient.mk (rawFactorIdeal R t a e) (rawDirection R r 1) = 1 at hp
    have hh : Ideal.Quotient.mk (rawFactorIdeal R t a e) (rawPair R t r 0) =
        Ideal.Quotient.mk (rawFactorIdeal R t a e) (rawPair R t r 1) *
          Ideal.Quotient.mk (rawFactorIdeal R t a e) (rawDirection R r 0) := by
      simpa [hp] using sub_eq_zero.mp h
    simpa using sub_eq_zero.mpr hh.symm

def slopeToRaw (t : R) (a : Fin 3) (e : Fin 4 → Fin 2) :
    SlopeRing R t a e →ₐ[R] RawFactorRing R t a e :=
  Ideal.Quotient.liftₐ _ (slopeBackEval R t a e) (by
    have h : slopeIdeal R t a e ≤ RingHom.ker (slopeBackEval R t a e).toRingHom :=
      Ideal.span_le.mpr (by rintro f ⟨r,rfl⟩; exact slopeBackEval_relation R t a e r)
    exact fun f hf => h hf)

@[simp] theorem slopeToRaw_mk (t : R) (a : Fin 3) (e : Fin 4 → Fin 2)
    (f : SlopePolynomial R) :
    slopeToRaw R t a e (Ideal.Quotient.mk _ f) = slopeBackEval R t a e f := rfl
end
end FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate.RawAdapter
