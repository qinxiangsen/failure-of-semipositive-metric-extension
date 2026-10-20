import FailureOfSemipositiveMetricExtension.CoordinateBlowupAdapter.RawInverseCoordinates

namespace FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate.RawAdapter
noncomputable section
open MvPolynomial
universe u
variable (R : Type u) [CommRing R]

@[simp] theorem rawToSlope_mk (t : R) (a : Fin 3) (e : Fin 4 → Fin 2)
    (f : RawFactorPolynomial R) :
    rawToSlope R t a e (Ideal.Quotient.mk _ f) = rawNormalization R t a e f := rfl

@[simp] theorem slopeToRaw_base (t : R) (a : Fin 3) (e : Fin 4 → Fin 2)
    (f : PairPolynomial R) :
    slopeToRaw R t a e (algebraMap (PairPolynomial R) (SlopeRing R t a e) f) =
      baseBack R t a e f := by
  change slopeToRaw R t a e (Ideal.Quotient.mk _ (C f)) = _
  simp

theorem slopeToRaw_direction (t : R) (a : Fin 3) (e : Fin 4 → Fin 2)
    (r : Fin 4) (b : Fin 2) :
    slopeToRaw R t a e (normalizedRawDirection R t a e r b) =
      Ideal.Quotient.mk _ (rawDirection R r b) := by
  by_cases hb : b = e r
  · subst b
    simp [raw_direction_pivot]
  · have ho : b = (e r).rev := by
      generalize e r = k at hb ⊢
      fin_cases b <;> fin_cases k <;> simp_all
    rw [normalizedRawDirection, if_neg hb, slopeToRaw_mk, slopeBackEval_X, ho]

theorem back_after_forward (t : R) (a : Fin 3) (e : Fin 4 → Fin 2) :
    (slopeToRaw R t a e).comp (rawToSlope R t a e) = AlgHom.id R _ := by
  apply Ideal.Quotient.algHom_ext
  ext i
  cases i with
  | inl b =>
    change slopeToRaw R t a e (rawNormalization R t a e (rawBase R b)) = _
    rw [rawNormalization_base, slopeToRaw_base, baseBack_vector]
    rfl
  | inr rb =>
    rcases rb with ⟨r,b⟩
    change slopeToRaw R t a e (rawNormalization R t a e (rawDirection R r b)) = _
    rw [rawNormalization_direction, slopeToRaw_direction]
    rfl

theorem forward_baseBack (t : R) (a : Fin 3) (e : Fin 4 → Fin 2) :
    (rawToSlope R t a e).comp (baseBack R t a e) =
      IsScalarTower.toAlgHom R (PairPolynomial R) (SlopeRing R t a e) := by
  ext j
  simp only [AlgHom.comp_apply, baseBack, aeval_X, rawToSlope_mk, rawNormalization_base]
  change algebraMap (PairPolynomial R) (SlopeRing R t a e)
    (normalizedVector R a (freeIndex a j)) =
    algebraMap (PairPolynomial R) (SlopeRing R t a e) (X j)
  congr 1
  fin_cases a <;> fin_cases j <;> rfl

theorem forward_after_back (t : R) (a : Fin 3) (e : Fin 4 → Fin 2) :
    (rawToSlope R t a e).comp (slopeToRaw R t a e) = AlgHom.id R _ := by
  apply Ideal.Quotient.algHom_ext
  ext r
  · change rawToSlope R t a e
      (slopeToRaw R t a e (algebraMap (PairPolynomial R) (SlopeRing R t a e) (X r))) =
      algebraMap (PairPolynomial R) (SlopeRing R t a e) (X r)
    rw [slopeToRaw_base]
    exact DFunLike.congr_fun (forward_baseBack R t a e) (X r)
  · simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      slopeToRaw_mk, slopeBackEval_X, rawToSlope_mk,
      rawNormalization_direction, normalizedRawDirection_other, AlgHom.id_apply]

/-- Exact coordinate-ring isomorphism on every original normalized projective
factor chart, with explicit inverse and no reducedness hypothesis. -/
def originalChartEquiv (t : R) (a : Fin 3) (e : Fin 4 → Fin 2) :
    RawFactorRing R t a e ≃ₐ[R] SlopeRing R t a e :=
  AlgEquiv.ofAlgHom (rawToSlope R t a e) (slopeToRaw R t a e)
    (forward_after_back R t a e) (back_after_forward R t a e)

@[simp] theorem originalChartEquiv_base (t : R) (a b : Fin 3) (e : Fin 4 → Fin 2) :
    originalChartEquiv R t a e (Ideal.Quotient.mk _ (rawBase R b)) =
      algebraMap (PairPolynomial R) (SlopeRing R t a e) (normalizedVector R a b) :=
  rawNormalization_base R t a b e

@[simp] theorem originalChartEquiv_direction (t : R) (a : Fin 3)
    (e : Fin 4 → Fin 2) (r : Fin 4) (b : Fin 2) :
    originalChartEquiv R t a e (Ideal.Quotient.mk _ (rawDirection R r b)) =
      normalizedRawDirection R t a e r b := rawNormalization_direction R t a e r b

@[simp] theorem originalChartEquiv_parameter (t c : R) (a : Fin 3) (e : Fin 4 → Fin 2) :
    originalChartEquiv R t a e (algebraMap R (RawFactorRing R t a e) c) =
      algebraMap R (SlopeRing R t a e) c := (originalChartEquiv R t a e).commutes c
end
end FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate.RawAdapter
