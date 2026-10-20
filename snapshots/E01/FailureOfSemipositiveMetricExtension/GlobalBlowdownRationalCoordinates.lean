import FailureOfSemipositiveMetricExtension.GlobalIncidenceEquations
import Mathlib.RingTheory.Localization.FractionRing

/-! Actual polynomial numerators, denominators, and fraction-field coordinates
for the inverse blow-down. These formulas are attached to the existing analytic
isomorphism, not to a separately postulated birational map. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.BlowdownComplement
noncomputable section
open Set MvPolynomial

abbrev AffinePolynomial := MvPolynomial (Fin 3) ℂ
abbrev AffineFunctionField := FractionRing AffinePolynomial

/-- Variables zero and one are affine plane coordinates, variable two is time. -/
def affineVector : Fin 3 → Fin 3 → AffinePolynomial
  | 0 => ![1,X 0,X 1]
  | 1 => ![X 0,1,X 1]
  | 2 => ![X 0,X 1,1]

def affinePair (a : Fin 3) : Fin 4 → Fin 2 → AffinePolynomial
  | 0 => ![affineVector a 1,affineVector a 2]
  | 1 => ![affineVector a 0,affineVector a 2]
  | 2 => ![affineVector a 1-affineVector a 0,affineVector a 2-X 2*affineVector a 0]
  | 3 => ![affineVector a 0,affineVector a 1]

@[simp] theorem affinePair_eval (a : Fin 3) (r : Fin 4) (e : Fin 2) (q : ℂ × ℂ) (t : ℂ) :
    eval ![q.1,q.2,t] (affinePair a r e) = pairMap r t (ProjectivePlane.vector a q) e := by
  fin_cases a <;> fin_cases r <;> fin_cases e <;>
    simp [affinePair,affineVector,ProjectivePlane.vector,pairMap,pair]

/-- No coordinate denominator is the zero polynomial; one common witness works
for all twenty-four affine expressions. -/
theorem affinePair_ne_zero (a : Fin 3) (r : Fin 4) (e : Fin 2) : affinePair a r e ≠ 0 := by
  intro h
  have he := affinePair_eval a r e (2,3) 5
  rw [h] at he
  simp only [map_zero] at he
  fin_cases a <;> fin_cases r <;> fin_cases e <;>
    norm_num [ProjectivePlane.vector,pairMap,pair,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at he

/-- An actual element of the fraction field of the affine three-space coordinate ring. -/
def inverseDirectionCoordinate (a : Fin 3) (r : Fin 4) (e : Fin 2) : AffineFunctionField :=
  algebraMap AffinePolynomial AffineFunctionField (affinePair a r e.rev) /
    algebraMap AffinePolynomial AffineFunctionField (affinePair a r e)

theorem inverseDirectionCoordinate_denominator_nonzero (a : Fin 3) (r : Fin 4) (e : Fin 2) :
    algebraMap AffinePolynomial AffineFunctionField (affinePair a r e) ≠ 0 := by
  simpa only [map_zero] using
    (IsFractionRing.injective AffinePolynomial AffineFunctionField).ne (affinePair_ne_zero a r e)

theorem inverseDirectionCoordinate_mul_denominator (a : Fin 3) (r : Fin 4) (e : Fin 2) :
    inverseDirectionCoordinate a r e *
      algebraMap AffinePolynomial AffineFunctionField (affinePair a r e) =
        algebraMap AffinePolynomial AffineFunctionField (affinePair a r e.rev) :=
  div_mul_cancel₀ _ (inverseDirectionCoordinate_denominator_nonzero a r e)

/-- The actual direction coordinate of the inverse is the displayed quotient
of polynomial evaluations wherever its denominator is nonzero. -/
theorem lift_direction_coordinate (a : Fin 3) (r : Fin 4) (e : Fin 2)
    (q : ℂ × ℂ) (t : ℂ)
    (haway : (ProjectivePlane.param a q,t) ∈ baseAway)
    (he : eval ![q.1,q.2,t] (affinePair a r e) ≠ 0) :
    ProjectiveLine.coordinates e (directions (lift (ProjectivePlane.param a q,t)) r) =
      eval ![q.1,q.2,t] (affinePair a r e.rev) /
        eval ![q.1,q.2,t] (affinePair a r e) := by
  simp only [lift_direction,Prod.fst,Prod.snd]
  rw [ProjectivePlane.param,chosenDirection_mk _ (ProjectivePlane.vector_nonzero a q) r t (haway r)]
  simp only [affinePair_eval] at he ⊢
  fin_cases e
  · change ProjectiveLine.coordinates 0 _ =
      pairMap r t (ProjectivePlane.vector a q) 1 / pairMap r t (ProjectivePlane.vector a q) 0
    rw [ProjectiveLine.vectorPoint_eq_param_zero _ he,ProjectiveLine.coordinates_param]
  · change ProjectiveLine.coordinates 1 _ =
      pairMap r t (ProjectivePlane.vector a q) 0 / pairMap r t (ProjectivePlane.vector a q) 1
    rw [ProjectiveLine.vectorPoint_eq_param_one _ he,ProjectiveLine.coordinates_param]

/-- The same quotient parametrizes the actual projective direction, and hence
also certifies that this is the right affine chart of the inverse. -/
theorem lift_direction_param (a : Fin 3) (r : Fin 4) (e : Fin 2)
    (q : ℂ × ℂ) (t : ℂ)
    (haway : (ProjectivePlane.param a q,t) ∈ baseAway)
    (he : eval ![q.1,q.2,t] (affinePair a r e) ≠ 0) :
    directions (lift (ProjectivePlane.param a q,t)) r = ProjectiveLine.param e
      (eval ![q.1,q.2,t] (affinePair a r e.rev) / eval ![q.1,q.2,t] (affinePair a r e)) := by
  simp only [lift_direction,Prod.fst,Prod.snd]
  rw [ProjectivePlane.param,chosenDirection_mk _ (ProjectivePlane.vector_nonzero a q) r t (haway r)]
  simp only [affinePair_eval] at he ⊢
  fin_cases e
  · exact ProjectiveLine.vectorPoint_eq_param_zero _ he
  · exact ProjectiveLine.vectorPoint_eq_param_one _ he

/-- Avoidance of all four moving centres is exactly the simultaneous exclusion
of four pairs of common polynomial zeros in each standard affine plane chart. -/
theorem baseAway_affine_iff (a : Fin 3) (q : ℂ × ℂ) (t : ℂ) :
    (ProjectivePlane.param a q,t) ∈ baseAway ↔
      ∀ r, eval ![q.1,q.2,t] (affinePair a r 0) ≠ 0 ∨
        eval ![q.1,q.2,t] (affinePair a r 1) ≠ 0 := by
  simp only [affinePair_eval]
  constructor
  · intro h r
    by_contra hn
    push_neg at hn
    have hz : pairMap r t (ProjectivePlane.vector a q) = 0 := by
      ext e
      fin_cases e
      · exact hn.1
      · exact hn.2
    exact pair_nonzero_of_mk_away _ (ProjectivePlane.vector_nonzero a q) r t (h r) hz
  · intro h r heq
    have hz : pairMap r t (ProjectivePlane.vector a q) = 0 :=
      (pairMap_zero_iff_mem_centre r t _).mpr
        ((projective_eq_iff_mem _ (ProjectivePlane.vector_nonzero a q) _).mp heq)
    rcases h r with h0 | h1
    · exact h0 (congrFun hz 0)
    · exact h1 (congrFun hz 1)

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.BlowdownComplement
