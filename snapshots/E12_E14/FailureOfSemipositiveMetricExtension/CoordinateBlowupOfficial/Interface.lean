/-
Unadmitted universal interface candidates. All statements below are proposition
DEFINITIONS, not axioms or asserted theorems. Independently elaborated in the
root-authorized isolated interface directory. The final narrowed candidate is
ActualReesUniversalPropertyStatement in CartierTranslation.lean.
-/
import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

universe u
namespace FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial

abbrev PairPolynomial (R : Type u) [CommRing R] := MvPolynomial (Fin 2) R

def pairIdeal {R : Type u} [CommRing R] (f g : R) : Ideal R :=
  Ideal.span ({f, g} : Set R)

def pairRelation {R : Type u} [CommRing R] (f g : R) : PairPolynomial R :=
  C f * X 1 - C g * X 0

abbrev PairQuotient {R : Type u} [CommRing R] (f g : R) :=
  PairPolynomial R ⧸ Ideal.span ({pairRelation f g} : Set (PairPolynomial R))

def pairEvaluation {R : Type u} [CommRing R] (f g : R) :
    PairPolynomial R →+* Polynomial R :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i : Fin 2 => Polynomial.monomial 1 (if i = 0 then f else g))

/-- Recommended narrower algebraic input: arbitrary coefficient ring, two
actual polynomial variables. Stacks 0G8Q, n = 2. No Noetherian hypothesis. -/
def CoordinatePairPresentationStatement : Prop :=
  ∀ (R : Type u) [CommRing R],
    let P := PairPolynomial R
    let x : P := X 0
    let y : P := X 1
    ∃ e : PairQuotient x y ≃ₐ[P] reesAlgebra (pairIdeal x y),
      ∀ h : PairPolynomial P,
        ((e (Ideal.Quotient.mk _ h) : reesAlgebra (pairIdeal x y)) : Polynomial P) =
          pairEvaluation x y h

/-- Exact grading semantics. Neither condition allows replacing the Rees
algebra or the incidence quotient by an unrelated ring. -/
def ReesGradeCondition {R : Type u} [CommRing R] (I : Ideal R)
    (G : ℕ → Submodule R (reesAlgebra I)) : Prop :=
  ∀ n p, p ∈ G n ↔ ∀ m, m ≠ n → (p : Polynomial R).coeff m = 0

def QuotientGradeCondition {R : Type u} [CommRing R] (f g : R)
    (G : ℕ → Submodule R (PairQuotient f g)) : Prop :=
  ∀ n q, q ∈ G n ↔
    ∃ h : PairPolynomial R,
      MvPolynomial.IsHomogeneous h n ∧ Ideal.Quotient.mk _ h = q

/-- Both grading instances and their semantic certificates must be constructed
in Lean before this statement has a concrete application. -/
def GradedCoordinatePresentationStatement : Prop :=
  ∀ (R : Type u) [CommRing R],
    let P := PairPolynomial R
    let x : P := X 0
    let y : P := X 1
    let I := pairIdeal x y
    ∀ (GQ : ℕ → Submodule P (PairQuotient x y)) [GradedAlgebra GQ]
      (GR : ℕ → Submodule P (reesAlgebra I)) [GradedAlgebra GR]
      (cQ : P →+* GQ 0) (cR : P →+* GR 0),
      QuotientGradeCondition x y GQ → ReesGradeCondition I GR →
      (∀ r, (cQ r : PairQuotient x y) = Ideal.Quotient.mk _ (C r)) →
      (∀ r, ((cR r : reesAlgebra I) : Polynomial P) = Polynomial.C r) →
      ∃ e : PairQuotient x y ≃ₐ[P] reesAlgebra I,
        (∀ h : PairPolynomial P,
          ((e (Ideal.Quotient.mk _ h) : reesAlgebra I) : Polynomial P) =
            pairEvaluation x y h) ∧
        ∃ θ : Proj GQ ≅ Proj GR,
          θ.hom ≫ Proj.toSpecZero GR ≫ Spec.map (CommRingCat.ofHom cR) =
            Proj.toSpecZero GQ ≫ Spec.map (CommRingCat.ofHom cQ) ∧
          ∀ i : Fin 2,
            θ.hom ⁻¹ᵁ Proj.basicOpen GR (e (Ideal.Quotient.mk _ (X i))) =
              Proj.basicOpen GQ (Ideal.Quotient.mk _ (X i))

/-- The ring map to an actual affine open of an arbitrary scheme is the
structure-sheaf pullback followed by restriction. -/
def affinePullback {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (b : Y ⟶ Spec (.of R)) (U : Y.affineOpens) : R →+* Γ(Y, U.1) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ b.appTop ≫
    Y.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op).hom

/-- Transparent local effective-Cartier condition for the inverse-image ideal.
Regularity means multiplication is injective; a merely principal ideal is
insufficient. Requiring this at every point includes the complement, where
one can use generator 1. -/
def CartierPullback {R : Type u} [CommRing R] (I : Ideal R)
    {Y : Scheme.{u}} (b : Y ⟶ Spec (.of R)) : Prop :=
  ∀ y : Y, ∃ U : Y.affineOpens, y ∈ U.1 ∧
    ∃ a : Γ(Y, U.1), _root_.IsRegular a ∧
      I.map (affinePullback b U) = Ideal.span ({a} : Set Γ(Y, U.1))

/-- Generic Proj-Rees universal property. This does not mention this paper,
its incidence scheme, its four centres, or its nonextension conclusion.
No finite generation is required by Stacks 0806. -/
def ReesUniversalPropertyStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Ideal R)
    (G : ℕ → Submodule R (reesAlgebra I)) [GradedAlgebra G]
    (c : R →+* G 0),
    ReesGradeCondition I G →
    (∀ r, ((c r : reesAlgebra I) : Polynomial R) = Polynomial.C r) →
    let b := Proj.toSpecZero G ≫ Spec.map (CommRingCat.ofHom c)
    CartierPullback I b ∧
      ∀ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of R)),
        CartierPullback I f → ∃! lift : Y ⟶ Proj G, lift ≫ b = f

end
end FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate
