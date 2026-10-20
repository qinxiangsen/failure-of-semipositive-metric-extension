import FailureOfSemipositiveMetricExtension.CoordinateBlowupOfficial.NormalizedFactorPresentation
import FailureOfSemipositiveMetricExtension.CoordinateBlowupOfficial.PreferredCentreAffineCover

/-! A four-member principal-open cover on each fixed normalized
incidence chart. Its denominators also put the retained centre in its preferred
projective block. It does not assume a normalization equivalence. -/
namespace FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate
noncomputable section
open MvPolynomial
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R]

theorem preferredCentreChart_surjective : Function.Surjective preferredCentreChart := by
  intro a
  fin_cases a
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨3,rfl⟩

/-- At any base prime, retain one centre, use its preferred nonzero projective
pivot, and exclude the other three centre ideals. -/
theorem preferredCentre_prime_cover (t : R) (a : Fin 3)
    (p : PrimeSpectrum (PairPolynomial R)) :
    ∃ r : Fin 4, normalizedVector R a (preferredCentreChart r) ∉ p.asIdeal ∧
      ∀ s : Fin 4, s ≠ r → ¬ normalizedCentreIdeal R t a s ≤ p.asIdeal := by
  classical
  by_cases h : ∃ r : Fin 4, normalizedCentreIdeal R t a r ≤ p.asIdeal
  · obtain ⟨r,hr⟩ := h
    refine ⟨r, ?_, fun s hs => normalizedCentres_not_both R t a p r s (Ne.symm hs) hr⟩
    exact (PrimeSpectrum.mem_basicOpen _ _).mp (normalizedCentre_preferred_open R t a r p hr)
  · obtain ⟨r,hr⟩ := preferredCentreChart_surjective a
    refine ⟨r, ?_, fun s _ hs => h ⟨s,hs⟩⟩
    rw [hr]
    have hp : normalizedVector R a a = 1 := by
      fin_cases a <;> simp [normalizedVector]
    rw [hp]
    intro h1
    exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

/-- In a fixed direction chart, noncontainment of a centre ideal forces its
selected pair component to remain nonzero at the prime. This removes the need
to change direction normalizations in the cover argument. -/
theorem selectedPair_not_mem_of_centre_not_le (t : R) (a : Fin 3)
    (e : Fin 4 → Fin 2) (r : Fin 4) (p : PrimeSpectrum (SlopeRing R t a e))
    (h : ¬ normalizedCentreIdeal R t a r ≤
      (PrimeSpectrum.comap (algebraMap (PairPolynomial R) (SlopeRing R t a e)) p).asIdeal) :
    algebraMap (PairPolynomial R) (SlopeRing R t a e) (normalizedPair R t a r (e r)) ∉
      p.asIdeal := by
  intro hs
  have hrel : algebraMap (PairPolynomial R) (SlopeRing R t a e)
      (normalizedPair R t a r (e r)) * Ideal.Quotient.mk _ (X r) =
      algebraMap (PairPolynomial R) (SlopeRing R t a e)
        (normalizedPair R t a r (e r).rev) := by
    apply sub_eq_zero.mp
    exact slope_relation_zero R t a e r
  have ho : algebraMap (PairPolynomial R) (SlopeRing R t a e)
      (normalizedPair R t a r (e r).rev) ∈ p.asIdeal := by
    rw [← hrel]
    exact p.asIdeal.mul_mem_right _ hs
  have hall : ∀ b : Fin 2, algebraMap (PairPolynomial R) (SlopeRing R t a e)
      (normalizedPair R t a r b) ∈ p.asIdeal := by
    intro b
    by_cases hb : b = e r
    · simpa only [hb] using hs
    · have hb' : b = (e r).rev := by
        generalize e r = c at hb ⊢
        fin_cases b <;> fin_cases c <;> simp_all
      simpa only [hb'] using ho
  apply h
  rw [normalizedCentreIdeal_le_iff]
  exact ⟨hall 0,hall 1⟩

/-- Coefficient denominator for a principal open in the actual unreduced slope
quotient. It combines a preferred base pivot with three fixed direction pivots. -/
def preferredIncidenceDenominator (t : R) (a : Fin 3) (e : Fin 4 → Fin 2) (r : Fin 4) :
    SlopeRing R t a e :=
  algebraMap (PairPolynomial R) (SlopeRing R t a e)
    (normalizedVector R a (preferredCentreChart r) * centreAvoidanceDenominator R t a r e)

/-- The precise next cover assertion concerns all prime ideals of the original
four-relation quotient, with no radical, pointwise-only reduction, or assumed
normalization equivalence. -/
theorem preferredIncidence_principal_open_cover (t : R) (a : Fin 3)
    (e : Fin 4 → Fin 2) (p : PrimeSpectrum (SlopeRing R t a e)) :
    ∃ r : Fin 4, p ∈ PrimeSpectrum.basicOpen (preferredIncidenceDenominator R t a e r) := by
  let q := PrimeSpectrum.comap (algebraMap (PairPolynomial R) (SlopeRing R t a e)) p
  obtain ⟨r,hp,hr⟩ := preferredCentre_prime_cover R t a q
  refine ⟨r, ?_⟩
  rw [PrimeSpectrum.mem_basicOpen]
  intro hmem
  rw [preferredIncidenceDenominator, map_mul] at hmem
  rcases p.isPrime.mem_or_mem hmem with hbase | hprod
  · exact hp hbase
  · rw [centreAvoidanceDenominator, map_prod] at hprod
    obtain ⟨s,hs,hmem⟩ := Ideal.IsPrime.prod_mem_iff.mp hprod
    exact selectedPair_not_mem_of_centre_not_le R t a e s p
      (hr s (Finset.mem_erase.mp hs).1) hmem

end
end FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate
