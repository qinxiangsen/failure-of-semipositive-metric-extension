import FailureOfSemipositiveMetricExtension.CoordinateBlowupOfficial.AffineCentreSeparation
import Mathlib.RingTheory.Localization.Away.Basic

/-! Explicit principal opens isolating at most one of the four centres.
The cover is proved on the full prime spectrum, and the three other centre
ideals become the unit ideal on each corresponding localization. -/
namespace FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate
noncomputable section
open MvPolynomial
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R]

theorem normalizedCentreIdeal_le_iff (t : R) (a : Fin 3) (r : Fin 4)
    (I : Ideal (PairPolynomial R)) :
    normalizedCentreIdeal R t a r ≤ I ↔
      normalizedPair R t a r 0 ∈ I ∧ normalizedPair R t a r 1 ∈ I := by
  simp [normalizedCentreIdeal, pairIdeal, Ideal.span_le, Set.insert_subset_iff,
    Set.singleton_subset_iff]

theorem normalizedPair_mem (t : R) (a : Fin 3) (r : Fin 4) (e : Fin 2) :
    normalizedPair R t a r e ∈ normalizedCentreIdeal R t a r := by
  unfold normalizedCentreIdeal pairIdeal
  fin_cases e <;> apply Ideal.subset_span <;> simp

def centreAvoidanceDenominator (t : R) (a : Fin 3) (r : Fin 4) (e : Fin 4 → Fin 2) :
    PairPolynomial R :=
  ∏ s ∈ Finset.univ.erase r, normalizedPair R t a s (e s)

/-- A finite, explicit principal-open cover of all scheme points of each base chart. -/
theorem centreAvoidance_principal_open_cover (t : R) (a : Fin 3)
    (p : PrimeSpectrum (PairPolynomial R)) :
    ∃ (r : Fin 4) (e : Fin 4 → Fin 2),
      p ∈ PrimeSpectrum.basicOpen (centreAvoidanceDenominator R t a r e) := by
  classical
  obtain ⟨r, hr⟩ := normalizedCentres_prime_cover R t a p
  have hs : ∀ s : Fin 4, ∃ e : Fin 2,
      s ≠ r → normalizedPair R t a s e ∉ p.asIdeal := by
    intro s
    by_cases hsr : s = r
    · exact ⟨0, fun h => (h hsr).elim⟩
    · have h := hr s hsr
      rw [normalizedCentreIdeal_le_iff] at h
      by_cases h0 : normalizedPair R t a s 0 ∈ p.asIdeal
      · exact ⟨1, fun _ h1 => h ⟨h0, h1⟩⟩
      · exact ⟨0, fun _ => h0⟩
  choose e he using hs
  refine ⟨r, e, ?_⟩
  rw [PrimeSpectrum.mem_basicOpen]
  intro h
  obtain ⟨s, hs, hmem⟩ := Ideal.IsPrime.prod_mem_iff.mp h
  exact he s (Finset.mem_erase.mp hs).1 hmem

abbrev CentreAvoidanceRing (t : R) (a : Fin 3) (r : Fin 4) (e : Fin 4 → Fin 2) :=
  Localization.Away (centreAvoidanceDenominator R t a r e)

theorem centreAvoidance_selected_isUnit (t : R) (a : Fin 3) (r : Fin 4)
    (e : Fin 4 → Fin 2) (s : Fin 4) (hs : s ≠ r) :
    IsUnit (algebraMap (PairPolynomial R) (CentreAvoidanceRing R t a r e)
      (normalizedPair R t a s (e s))) := by
  apply IsLocalization.Away.isUnit_of_dvd (centreAvoidanceDenominator R t a r e)
  exact Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hs, Finset.mem_univ s⟩)

/-- The full scheme-theoretic inverse image of each other centre is empty. -/
theorem centreAvoidance_other_ideal_top (t : R) (a : Fin 3) (r : Fin 4)
    (e : Fin 4 → Fin 2) (s : Fin 4) (hs : s ≠ r) :
    (normalizedCentreIdeal R t a s).map
      (algebraMap (PairPolynomial R) (CentreAvoidanceRing R t a r e)) = ⊤ := by
  exact Ideal.eq_top_of_isUnit_mem _
    (Ideal.mem_map_of_mem _ (normalizedPair_mem R t a s (e s)))
    (centreAvoidance_selected_isUnit R t a r e s hs)

end
end FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate
