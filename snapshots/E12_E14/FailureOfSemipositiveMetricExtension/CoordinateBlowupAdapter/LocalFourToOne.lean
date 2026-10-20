import FailureOfSemipositiveMetricExtension.CoordinateBlowupAdapter.RawCoordinateEquivalence

/-! Exact four-to-one equation reduction on the actual localized slope ring.
This file supplies the missing coefficient-localization adapter and then uses
 the already accepted centreDirectionEliminationEquiv. -/
namespace FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate.RawAdapter.LocalReduction
noncomputable section
open MvPolynomial
universe u
variable (R : Type u) [CommRing R] (t : R) (a : Fin 3) (r : Fin 4) (e : Fin 4 → Fin 2)

abbrev Coeff := CentreAvoidanceRing R t a r e
abbrev Data := centreDirectionEliminationData R t a r e
abbrev Many := (Data R t a r e).ManyRing
abbrev One := (Data R t a r e).OneRing

def denom : SlopeRing R t a e :=
  algebraMap (PairPolynomial R) (SlopeRing R t a e) (centreAvoidanceDenominator R t a r e)
abbrev Local := Localization.Away (denom R t a r e)

def pairToMany : PairPolynomial R →+* Many R t a r e :=
  (algebraMap (Coeff R t a r e) (Many R t a r e)).comp
    (algebraMap (PairPolynomial R) (Coeff R t a r e))

def slopeToManyEval : SlopePolynomial R →+* Many R t a r e :=
  eval₂Hom (pairToMany R t a r e) (fun s => Ideal.Quotient.mk _ (X s))

theorem slopeToManyEval_relation (s : Fin 4) :
    slopeToManyEval R t a r e (slopeRelation R t a e s) = 0 := by
  simpa [slopeToManyEval, slopeRelation, pairToMany,
    DirectionEliminationData.manyRelation, Data, centreDirectionEliminationData]
    using (Data R t a r e).many_relation_zero s

def slopeToMany : SlopeRing R t a e →+* Many R t a r e :=
  Ideal.Quotient.lift _ (slopeToManyEval R t a r e) (by
    have h : slopeIdeal R t a e ≤ RingHom.ker (slopeToManyEval R t a r e) :=
      Ideal.span_le.mpr (by rintro f ⟨s,rfl⟩; exact slopeToManyEval_relation R t a r e s)
    exact fun f hf => h hf)

@[simp] theorem slopeToMany_mk (f : SlopePolynomial R) :
    slopeToMany R t a r e (Ideal.Quotient.mk _ f) = slopeToManyEval R t a r e f := rfl
@[simp] theorem slopeToMany_coeff (f : PairPolynomial R) :
    slopeToMany R t a r e (algebraMap (PairPolynomial R) (SlopeRing R t a e) f) =
      pairToMany R t a r e f := by
  change slopeToManyEval R t a r e (C f) = _
  simp [slopeToManyEval]
@[simp] theorem slopeToMany_X (s : Fin 4) :
    slopeToMany R t a r e (Ideal.Quotient.mk _ (X s)) = Ideal.Quotient.mk _ (X s) := by
  simp [slopeToMany, slopeToManyEval]

theorem slopeToMany_denom_unit : IsUnit (slopeToMany R t a r e (denom R t a r e)) := by
  rw [denom, slopeToMany_coeff]
  exact (IsLocalization.Away.algebraMap_isUnit (S := Coeff R t a r e)
    (centreAvoidanceDenominator R t a r e)).map
    (algebraMap (Coeff R t a r e) (Many R t a r e))

def localToMany : Local R t a r e →+* Many R t a r e :=
  IsLocalization.Away.lift (denom R t a r e) (slopeToMany_denom_unit R t a r e)

@[simp] theorem localToMany_algebraMap (f : SlopeRing R t a e) :
    localToMany R t a r e (algebraMap (SlopeRing R t a e) (Local R t a r e) f) =
      slopeToMany R t a r e f := IsLocalization.Away.lift_eq _ _ _

def pairToLocal : PairPolynomial R →+* Local R t a r e :=
  (algebraMap (SlopeRing R t a e) (Local R t a r e)).comp
    (algebraMap (PairPolynomial R) (SlopeRing R t a e))

def coeffToLocal : Coeff R t a r e →+* Local R t a r e :=
  IsLocalization.Away.lift (centreAvoidanceDenominator R t a r e)
    (show IsUnit (pairToLocal R t a r e (centreAvoidanceDenominator R t a r e)) from
      IsLocalization.Away.algebraMap_isUnit (denom R t a r e))

@[simp] theorem coeffToLocal_algebraMap (f : PairPolynomial R) :
    coeffToLocal R t a r e (algebraMap (PairPolynomial R) (Coeff R t a r e) f) =
      pairToLocal R t a r e f := IsLocalization.Away.lift_eq _ _ _

def manyToLocalEval : MvPolynomial (Fin 4) (Coeff R t a r e) →+* Local R t a r e :=
  eval₂Hom (coeffToLocal R t a r e)
    (fun s => algebraMap (SlopeRing R t a e) (Local R t a r e) (Ideal.Quotient.mk _ (X s)))

set_option synthInstance.maxHeartbeats 100000 in
theorem manyToLocalEval_relation (s : Fin 4) :
    manyToLocalEval R t a r e ((Data R t a r e).manyRelation s) = 0 := by
  change manyToLocalEval R t a r e
    (C (algebraMap (PairPolynomial R) (Coeff R t a r e) (normalizedPair R t a s (e s))) * X s -
      C (algebraMap (PairPolynomial R) (Coeff R t a r e) (normalizedPair R t a s (e s).rev))) = 0
  simp only [manyToLocalEval, map_sub, map_mul, eval₂Hom_C, eval₂Hom_X',
    coeffToLocal_algebraMap]
  have h := congrArg (algebraMap (SlopeRing R t a e) (Local R t a r e))
    (slope_relation_zero R t a e s)
  simpa only [slopeRelation, map_sub, map_mul, map_zero] using h

def manyToLocal : Many R t a r e →+* Local R t a r e :=
  Ideal.Quotient.lift _ (manyToLocalEval R t a r e) (by
    have h : (Data R t a r e).manyIdeal ≤ RingHom.ker (manyToLocalEval R t a r e) :=
      Ideal.span_le.mpr (by rintro f ⟨s,rfl⟩; exact manyToLocalEval_relation R t a r e s)
    exact fun f hf => h hf)

@[simp] theorem manyToLocal_mk (f : MvPolynomial (Fin 4) (Coeff R t a r e)) :
    manyToLocal R t a r e (Ideal.Quotient.mk _ f) = manyToLocalEval R t a r e f := rfl
@[simp] theorem manyToLocal_coeff (f : Coeff R t a r e) :
    manyToLocal R t a r e (algebraMap (Coeff R t a r e) (Many R t a r e) f) =
      coeffToLocal R t a r e f := by
  change manyToLocal R t a r e (Ideal.Quotient.mk _ (C f)) = _
  simp [manyToLocalEval]
@[simp] theorem manyToLocal_X (s : Fin 4) :
    manyToLocal R t a r e (Ideal.Quotient.mk _ (X s)) =
      algebraMap (SlopeRing R t a e) (Local R t a r e) (Ideal.Quotient.mk _ (X s)) :=
  by simp [manyToLocal, manyToLocalEval]

end
end FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate.RawAdapter.LocalReduction
