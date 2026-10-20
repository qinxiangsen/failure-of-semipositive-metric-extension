import FailureOfSemipositiveMetricExtension.CoordinateBlowupOfficial.AffineCentreOpenCover

/-! The preferred affine block contains the whole centre as a scheme-theoretic
closed locus. In particular the moving centre is handled in the x=1 block;
no arbitrary normalized pair is silently treated as a coordinate pair. -/
namespace FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate
noncomputable section
open MvPolynomial
universe u
variable (R : Type u) [CommRing R]

def preferredCentreChart : Fin 4 → Fin 3
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 2

/-- The centre and the complement of its preferred projective block are disjoint,
proved by explicit ideal membership over every coefficient ring. -/
theorem normalizedCentre_preferred_comaximal (t : R) (a : Fin 3) (r : Fin 4) :
    normalizedCentreIdeal R t a r ⊔
      Ideal.span {normalizedVector R a (preferredCentreChart r)} = ⊤ := by
  let J := normalizedCentreIdeal R t a r ⊔
    Ideal.span {normalizedVector R a (preferredCentreChart r)}
  have h0 : normalizedPair R t a r 0 ∈ J :=
    Ideal.mem_sup_left (normalizedPair_mem R t a r 0)
  have h1 : normalizedPair R t a r 1 ∈ J :=
    Ideal.mem_sup_left (normalizedPair_mem R t a r 1)
  have hp : normalizedVector R a (preferredCentreChart r) ∈ J :=
    Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _))
  apply (Ideal.eq_top_iff_one _).mpr
  change (1 : PairPolynomial R) ∈ J
  fin_cases r <;> fin_cases a <;>
    simp only [preferredCentreChart, normalizedVector, normalizedPair, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two] at h0 h1 hp
  all_goals dsimp at h0 h1 hp
  all_goals first | exact hp | exact h0 | exact h1 | skip
  · convert J.add_mem h0 hp using 1 <;> ring
  · change 1 - C t * X 0 ∈ J at h1
    convert J.add_mem h1 (J.mul_mem_left (C t) hp) using 1 <;> ring

/-- Every prime over a centre is in its preferred affine block. -/
theorem normalizedCentre_preferred_open (t : R) (a : Fin 3) (r : Fin 4)
    (p : PrimeSpectrum (PairPolynomial R))
    (h : normalizedCentreIdeal R t a r ≤ p.asIdeal) :
    p ∈ PrimeSpectrum.basicOpen (normalizedVector R a (preferredCentreChart r)) := by
  rw [PrimeSpectrum.mem_basicOpen]
  intro hp
  have htop : (⊤ : Ideal (PairPolynomial R)) ≤ p.asIdeal := by
    rw [← normalizedCentre_preferred_comaximal R t a r]
    exact sup_le h (Ideal.span_le.mpr (fun q hq => by simpa only [Set.mem_singleton_iff.mp hq] using hp))
  exact p.isPrime.ne_top (top_unique htop)

end
end FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate
