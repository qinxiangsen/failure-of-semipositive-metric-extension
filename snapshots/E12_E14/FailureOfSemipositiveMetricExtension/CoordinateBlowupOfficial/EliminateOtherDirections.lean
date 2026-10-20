import FailureOfSemipositiveMetricExtension.CoordinateBlowupOfficial.AffineCentreOpenCover

/-! Exact elimination of the other three directions, while retaining the
possibly exceptional direction. The original four-equation ideal is used,
without passing to radicals. -/
namespace FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate
noncomputable section
open MvPolynomial
universe u
variable (R : Type u) [CommRing R]

structure DirectionEliminationData where
  pivot : Fin 4
  denominator : Fin 4 → R
  numerator : Fin 4 → R
  other_isUnit : ∀ s, s ≠ pivot → IsUnit (denominator s)

namespace DirectionEliminationData
variable {R} (D : DirectionEliminationData R)

abbrev ManyPolynomial := MvPolynomial (Fin 4) R
abbrev OnePolynomial := MvPolynomial (Fin 1) R

def manyRelation (s : Fin 4) : ManyPolynomial (R := R) :=
  C (D.denominator s) * X s - C (D.numerator s)

def oneRelation : OnePolynomial (R := R) :=
  C (D.denominator D.pivot) * X 0 - C (D.numerator D.pivot)

def manyIdeal : Ideal (ManyPolynomial (R := R)) := Ideal.span (Set.range D.manyRelation)
def oneIdeal : Ideal (OnePolynomial (R := R)) := Ideal.span {D.oneRelation}
abbrev ManyRing := ManyPolynomial (R := R) ⧸ D.manyIdeal
abbrev OneRing := OnePolynomial (R := R) ⧸ D.oneIdeal

def solvedSlope (s : Fin 4) : R :=
  if h : s = D.pivot then 0 else ↑(D.other_isUnit s h).unit⁻¹ * D.numerator s

theorem denominator_solvedSlope (s : Fin 4) (hs : s ≠ D.pivot) :
    D.denominator s * D.solvedSlope s = D.numerator s := by
  rw [solvedSlope, dif_neg hs]
  calc
    D.denominator s * (↑(D.other_isUnit s hs).unit⁻¹ * D.numerator s) =
        ↑(D.other_isUnit s hs).unit *
          (↑(D.other_isUnit s hs).unit⁻¹ * D.numerator s) :=
      congrArg (fun x : R => x * (↑(D.other_isUnit s hs).unit⁻¹ * D.numerator s))
        (D.other_isUnit s hs).unit_spec.symm
    _ = D.numerator s := by simp [← mul_assoc]

def manyEvaluation : ManyPolynomial (R := R) →ₐ[R] D.OneRing :=
  aeval fun s => if s = D.pivot then Ideal.Quotient.mk D.oneIdeal (X 0)
    else algebraMap R D.OneRing (D.solvedSlope s)

def oneEvaluation : OnePolynomial (R := R) →ₐ[R] D.ManyRing :=
  aeval fun _ => Ideal.Quotient.mk D.manyIdeal (X D.pivot)

theorem many_relation_zero (s : Fin 4) :
    Ideal.Quotient.mk D.manyIdeal (D.manyRelation s) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨s, rfl⟩)

theorem one_relation_zero : Ideal.Quotient.mk D.oneIdeal D.oneRelation = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

theorem manyEvaluation_relation (s : Fin 4) : D.manyEvaluation (D.manyRelation s) = 0 := by
  by_cases hs : s = D.pivot
  · subst s
    simpa [manyEvaluation, manyRelation, oneRelation] using D.one_relation_zero
  · simp only [manyEvaluation, manyRelation, map_sub, map_mul, aeval_C, aeval_X, if_neg hs]
    change algebraMap R D.OneRing (D.denominator s) *
      algebraMap R D.OneRing (D.solvedSlope s) - algebraMap R D.OneRing (D.numerator s) = 0
    rw [← map_mul, D.denominator_solvedSlope s hs, sub_self]

theorem oneEvaluation_relation : D.oneEvaluation D.oneRelation = 0 := by
  simpa [oneEvaluation, oneRelation, manyRelation] using D.many_relation_zero D.pivot

def manyToOne : D.ManyRing →ₐ[R] D.OneRing :=
  Ideal.Quotient.liftₐ D.manyIdeal D.manyEvaluation (by
    have h : D.manyIdeal ≤ RingHom.ker D.manyEvaluation.toRingHom := by
      rw [manyIdeal, Ideal.span_le]
      rintro _ ⟨s, rfl⟩
      exact D.manyEvaluation_relation s
    exact fun f hf => h hf)

def oneToMany : D.OneRing →ₐ[R] D.ManyRing :=
  Ideal.Quotient.liftₐ D.oneIdeal D.oneEvaluation (by
    have h : D.oneIdeal ≤ RingHom.ker D.oneEvaluation.toRingHom := by
      rw [oneIdeal, Ideal.span_le]
      rintro f (rfl : f = _)
      exact D.oneEvaluation_relation
    exact fun f hf => h hf)

@[simp] theorem manyToOne_mk (f : ManyPolynomial (R := R)) :
    D.manyToOne (Ideal.Quotient.mk _ f) = D.manyEvaluation f := rfl

@[simp] theorem oneToMany_mk (f : OnePolynomial (R := R)) :
    D.oneToMany (Ideal.Quotient.mk _ f) = D.oneEvaluation f := rfl

/-- The three eliminable direction coordinates equal their proved quotients. -/
theorem many_mk_other (s : Fin 4) (hs : s ≠ D.pivot) :
    Ideal.Quotient.mk D.manyIdeal (X s) = algebraMap R D.ManyRing (D.solvedSlope s) := by
  apply ((D.other_isUnit s hs).map (algebraMap R D.ManyRing)).isRegular.left
  have h := D.many_relation_zero s
  have hrel : algebraMap R D.ManyRing (D.denominator s) *
      Ideal.Quotient.mk D.manyIdeal (X s) = algebraMap R D.ManyRing (D.numerator s) := by
    simpa only [manyRelation, map_sub, map_mul, sub_eq_zero] using h
  change algebraMap R D.ManyRing (D.denominator s) * Ideal.Quotient.mk _ (X s) =
    algebraMap R D.ManyRing (D.denominator s) * algebraMap R D.ManyRing (D.solvedSlope s)
  erw [hrel, ← map_mul, D.denominator_solvedSlope s hs]

theorem manyToOne_comp : D.manyToOne.comp D.oneToMany = AlgHom.id R _ := by
  apply Ideal.Quotient.algHom_ext
  ext i
  fin_cases i
  simp [oneEvaluation, manyEvaluation]

theorem oneToMany_comp : D.oneToMany.comp D.manyToOne = AlgHom.id R _ := by
  apply Ideal.Quotient.algHom_ext
  ext s
  by_cases hs : s = D.pivot
  · subst s
    simp [oneEvaluation, manyEvaluation]
  · simpa [manyEvaluation, hs] using (D.many_mk_other s hs).symm

/-- Exact R-algebra equivalence retaining the exceptional direction relation. -/
def eliminationEquiv : D.ManyRing ≃ₐ[R] D.OneRing :=
  AlgEquiv.ofAlgHom D.manyToOne D.oneToMany D.manyToOne_comp D.oneToMany_comp

@[simp] theorem eliminationEquiv_mk (f : ManyPolynomial (R := R)) :
    D.eliminationEquiv (Ideal.Quotient.mk _ f) = D.manyEvaluation f := rfl

@[simp] theorem eliminationEquiv_selected :
    D.eliminationEquiv (Ideal.Quotient.mk D.manyIdeal (X D.pivot)) =
      Ideal.Quotient.mk D.oneIdeal (X 0) := by
  simp [manyEvaluation]

@[simp] theorem eliminationEquiv_other (s : Fin 4) (hs : s ≠ D.pivot) :
    D.eliminationEquiv (Ideal.Quotient.mk D.manyIdeal (X s)) =
      algebraMap R D.OneRing (D.solvedSlope s) := by
  simp [manyEvaluation, hs]

@[simp] theorem eliminationEquiv_C (c : R) :
    D.eliminationEquiv (Ideal.Quotient.mk D.manyIdeal (C c)) =
      algebraMap R D.OneRing c := by
  simp [manyEvaluation]

@[simp] theorem eliminationEquiv_symm_selected :
    D.eliminationEquiv.symm (Ideal.Quotient.mk D.oneIdeal (X 0)) =
      Ideal.Quotient.mk D.manyIdeal (X D.pivot) := by
  change D.oneToMany (Ideal.Quotient.mk _ (X 0)) = _
  simp [oneEvaluation]

open AlgebraicGeometry CategoryTheory in
/-- The exact quotient equivalence induces an isomorphism of actual schemes. -/
def eliminationSchemeIso : Spec (.of D.ManyRing) ≅ Spec (.of D.OneRing) :=
  (Scheme.Spec.mapIso D.eliminationEquiv.toRingEquiv.toCommRingCatIso.op).symm

open AlgebraicGeometry CategoryTheory in
/-- The scheme isomorphism lies over the original affine coefficient base. -/
theorem eliminationSchemeIso_projection :
    D.eliminationSchemeIso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R D.OneRing)) =
      Spec.map (CommRingCat.ofHom (algebraMap R D.ManyRing)) := by
  change Spec.map (CommRingCat.ofHom D.eliminationEquiv.symm.toRingHom) ≫ _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext c
  exact D.eliminationEquiv.symm.commutes c

end DirectionEliminationData

/-- The unit hypotheses are supplied by the explicit all-prime centre cover,
not assumed for the paper's four direction pairs. -/
def centreDirectionEliminationData (t : R) (a : Fin 3) (r : Fin 4)
    (e : Fin 4 → Fin 2) : DirectionEliminationData (CentreAvoidanceRing R t a r e) where
  pivot := r
  denominator s := algebraMap (PairPolynomial R) (CentreAvoidanceRing R t a r e)
    (normalizedPair R t a s (e s))
  numerator s := algebraMap (PairPolynomial R) (CentreAvoidanceRing R t a r e)
    (normalizedPair R t a s (e s).rev)
  other_isUnit s hs := centreAvoidance_selected_isUnit R t a r e s hs

/-- The four original normalized equations reduce to one selected equation
on each of the explicitly proved principal opens. -/
def centreDirectionEliminationEquiv (t : R) (a : Fin 3) (r : Fin 4)
    (e : Fin 4 → Fin 2) :
    (centreDirectionEliminationData R t a r e).ManyRing ≃ₐ[CentreAvoidanceRing R t a r e]
      (centreDirectionEliminationData R t a r e).OneRing :=
  (centreDirectionEliminationData R t a r e).eliminationEquiv

end
end FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate
