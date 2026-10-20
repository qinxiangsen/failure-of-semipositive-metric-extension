import FailureOfSemipositiveMetricExtension.CentralCubicDivision

/-! A verified exceptional-division constructor on the actual central surface.
Its input explicitly contains the genuine denominator/numerator and all polynomial
factorization proofs; the gluing and extension across exceptional curves are derived. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold
open scoped Manifold ContDiff

theorem scalarPower_contMDiffOn {t : ℂ} {U : Set (Fiber t)} {f : Fiber t → ℂ}
    (hf : ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω f U) (m : ℕ) :
    ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω (fun p => f p ^ m) U := by
  induction m with
  | zero => simpa using (contMDiffOn_const (c := (1 : ℂ)))
  | succ m ih => simpa only [pow_succ,smul_eq_mul] using ih.smul hf

structure WeightedDivisionData (a c : ℤ) (b d : Fin 4 → ℤ) where
  multiplicity : Fin 4 → ℕ
  denominator : SectionData 0 c d
  numerator : SectionData 0 (a+c) (fun r => b r+d r)
  denominator_coefficient : ∀ i p, denominator.coefficient i p =
    ∏ r, exceptionalCoefficient 0 r i p ^ multiplicity r
  localCoefficient : Fin 4 → Fin 2 → FixedFiber.Coord → ℂ
  localCoefficient_analytic : ∀ r e, ContDiff ℂ ω (localCoefficient r e)
  pullback_identity : ∀ (j : DivisionIndex) (q : FixedFiber.Coord),
    numerator.coefficient (divisionFrame j) (FixedFiber.param 0 j.1 j.2.1 q) =
      q.1 ^ multiplicity j.1 * localCoefficient j.1 j.2.1 q

namespace WeightedDivisionData
variable {a c : ℤ} {b d : Fin 4 → ℤ} (D : WeightedDivisionData a c b d)

def otherDenominator (j : DivisionIndex) (p : Fiber 0) : ℂ :=
  ∏ r ∈ Finset.univ.erase j.1, exceptionalCoefficient 0 r (divisionFrame j) p ^ D.multiplicity r

theorem denominator_ne_zero (p : Fiber 0) (hp : p ∈ FixedFiber.awayCentres 0)
    (i : Index) (hi : p ∈ baseSet 0 i) : D.denominator.coefficient i p ≠ 0 := by
  rw [D.denominator_coefficient]
  apply Finset.prod_ne_zero_iff.mpr
  intro r _
  apply pow_ne_zero
  intro hz
  exact hp r ((exceptionalCoefficient_zero_iff 0 r i p hi).mp hz)

theorem otherDenominator_ne_zero (j : DivisionIndex) (p : Fiber 0)
    (hp : p ∈ divisionPatch 0 j) : D.otherDenominator j p ≠ 0 := by
  unfold otherDenominator
  apply Finset.prod_ne_zero_iff.mpr
  intro r hr
  apply pow_ne_zero
  intro hz
  exact divisionPatch_avoids_other_centres 0 j p hp r (Finset.mem_erase.mp hr).1
    ((exceptionalCoefficient_zero_iff 0 r (divisionFrame j) p hp.2).mp hz)

theorem otherDenominator_contMDiffOn (j : DivisionIndex) :
    ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω (D.otherDenominator j) (divisionPatch 0 j) := by
  apply scalarProduct_contMDiffOn
  intro r _
  exact scalarPower_contMDiffOn
    ((exceptionalCoefficient_contMDiffOn 0 r (divisionFrame j)).mono
      (divisionPatch_subset_frame 0 j)) _

def localQuotient (j : DivisionIndex) (p : Fiber 0) : ℂ :=
  D.localCoefficient j.1 j.2.1 (FixedFiber.coordinates 0 j.1 j.2.1 p) / D.otherDenominator j p

theorem localQuotient_contMDiffOn (j : DivisionIndex) :
    ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω (D.localQuotient j) (divisionPatch 0 j) := by
  have hn := (D.localCoefficient_analytic j.1 j.2.1).contMDiff.comp_contMDiffOn
    ((FixedFiber.coordinates_contMDiffOn 0 j.1 j.2.1 ω).mono (divisionPatch_subset_source 0 j))
  have hinv : ContDiffOn ℂ ω (fun z : ℂ => z⁻¹) {z | z ≠ 0} :=
    contDiffOn_id.inv (fun _ h => h)
  have hd : ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω
      (fun p => (D.otherDenominator j p)⁻¹) (divisionPatch 0 j) :=
    hinv.contMDiffOn.comp (D.otherDenominator_contMDiffOn j)
      (fun p hp => D.otherDenominator_ne_zero j p hp)
  simpa only [localQuotient,div_eq_mul_inv,Function.comp_apply,smul_eq_mul] using hn.smul hd

theorem localQuotient_identity (j : DivisionIndex) (p : Fiber 0) (hp : p ∈ divisionPatch 0 j) :
    D.localQuotient j p * D.denominator.coefficient (divisionFrame j) p =
      D.numerator.coefficient (divisionFrame j) p := by
  have hD := D.otherDenominator_ne_zero j p hp
  have he : D.denominator.coefficient (divisionFrame j) p =
      exceptionalCoefficient 0 j.1 (divisionFrame j) p ^ D.multiplicity j.1 * D.otherDenominator j p := by
    rw [D.denominator_coefficient]
    exact (Finset.mul_prod_erase Finset.univ
      (fun r => exceptionalCoefficient 0 r (divisionFrame j) p ^ D.multiplicity r)
      (Finset.mem_univ j.1)).symm
  have hq := FixedFiber.param_coordinates 0 j.1 j.2.1 p hp.1
  have hE : exceptionalCoefficient 0 j.1 (divisionFrame j) p =
      (FixedFiber.coordinates 0 j.1 j.2.1 p).1 := by
    conv_lhs => rw [← hq]
    exact exceptionalCoefficient_param 0 j _
  have hN : D.numerator.coefficient (divisionFrame j) p =
      (FixedFiber.coordinates 0 j.1 j.2.1 p).1 ^ D.multiplicity j.1 *
        D.localCoefficient j.1 j.2.1 (FixedFiber.coordinates 0 j.1 j.2.1 p) := by
    conv_lhs => rw [← hq]
    exact D.pullback_identity j _
  rw [he,hE,hN]
  unfold localQuotient
  field_simp
  ring

/-- The actual analytic quotient section, without any assumed divisibility or gluing theorem. -/
def quotientSection : SectionData 0 a b :=
  divideSections D.denominator D.numerator (FixedFiber.awayCentres 0)
    (FixedFiber.awayCentres_dense 0) D.denominator_ne_zero
    (divisionPatch 0) (divisionPatch_isOpen 0) (divisionPatch_cover 0)
    divisionFrame (divisionPatch_subset_frame 0) D.localQuotient
    D.localQuotient_contMDiffOn D.localQuotient_identity

theorem quotientSection_coefficient (j : DivisionIndex) (p : Fiber 0) (hp : p ∈ divisionPatch 0 j) :
    D.quotientSection.coefficient (divisionFrame j) p = D.localQuotient j p := by
  have h := divideSections_coefficient D.denominator D.numerator (FixedFiber.awayCentres 0)
    (FixedFiber.awayCentres_dense 0) D.denominator_ne_zero
    (divisionPatch 0) (divisionPatch_isOpen 0) (divisionPatch_cover 0)
    divisionFrame (divisionPatch_subset_frame 0) D.localQuotient
    D.localQuotient_contMDiffOn D.localQuotient_identity j (divisionFrame j) p hp hp.2
  simpa only [gain_self,one_mul] using h

theorem quotientSection_division (i : Index) (p : Fiber 0) (hi : p ∈ baseSet 0 i) :
    D.quotientSection.coefficient i p * D.denominator.coefficient i p = D.numerator.coefficient i p :=
  divideSections_mul_coefficient D.denominator D.numerator (FixedFiber.awayCentres 0)
    (FixedFiber.awayCentres_dense 0) D.denominator_ne_zero
    (divisionPatch 0) (divisionPatch_isOpen 0) (divisionPatch_cover 0)
    divisionFrame (divisionPatch_subset_frame 0) D.localQuotient
    D.localQuotient_contMDiffOn D.localQuotient_identity i p hi

theorem quotientSection_division_sectionMap :
    sectionMap (multiplySections D.quotientSection D.denominator) = sectionMap D.numerator :=
  divideSections_mul_sectionMap D.denominator D.numerator (FixedFiber.awayCentres 0)
    (FixedFiber.awayCentres_dense 0) D.denominator_ne_zero
    (divisionPatch 0) (divisionPatch_isOpen 0) (divisionPatch_cover 0)
    divisionFrame (divisionPatch_subset_frame 0) D.localQuotient
    D.localQuotient_contMDiffOn D.localQuotient_identity
end WeightedDivisionData
end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
