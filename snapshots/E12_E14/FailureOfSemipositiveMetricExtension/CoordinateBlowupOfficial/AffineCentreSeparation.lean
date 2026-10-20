import FailureOfSemipositiveMetricExtension.CoordinateBlowupOfficial.Interface

/-! Scheme-theoretic separation of the four explicit centres on each standard
projective affine chart. This is an ideal identity over any coefficient ring,
including rings with nilpotents, so it is not only a statement about complex
closed points. The parameter is an arbitrary element of the coefficient ring. -/
namespace FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate
noncomputable section
open MvPolynomial
universe u
variable (R : Type u) [CommRing R]

def normalizedVector : Fin 3 → Fin 3 → PairPolynomial R
  | 0 => ![1, X 0, X 1]
  | 1 => ![X 0, 1, X 1]
  | 2 => ![X 0, X 1, 1]

def normalizedPair (t : R) (a : Fin 3) : Fin 4 → Fin 2 → PairPolynomial R
  | 0 => ![normalizedVector R a 1, normalizedVector R a 2]
  | 1 => ![normalizedVector R a 0, normalizedVector R a 2]
  | 2 => ![normalizedVector R a 1 - normalizedVector R a 0,
      normalizedVector R a 2 - C t * normalizedVector R a 0]
  | 3 => ![normalizedVector R a 0, normalizedVector R a 1]

def normalizedCentreIdeal (t : R) (a : Fin 3) (r : Fin 4) : Ideal (PairPolynomial R) :=
  pairIdeal (normalizedPair R t a r 0) (normalizedPair R t a r 1)

private theorem span_pair_sub_one_sup (x y z : PairPolynomial R) :
    Ideal.span {x, y} ⊔ Ideal.span {x - 1, z} = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have hx : x ∈ Ideal.span {x, y} ⊔ Ideal.span {x - 1, z} :=
    Ideal.mem_sup_left (Ideal.subset_span (by simp))
  have hy : x - 1 ∈ Ideal.span {x, y} ⊔ Ideal.span {x - 1, z} :=
    Ideal.mem_sup_right (Ideal.subset_span (by simp))
  simpa using Ideal.sub_mem _ hx hy

private theorem span_pair_one_sub_sup (x y z : PairPolynomial R) :
    Ideal.span {x, y} ⊔ Ideal.span {1 - x, z} = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have hx : x ∈ Ideal.span {x, y} ⊔ Ideal.span {1 - x, z} :=
    Ideal.mem_sup_left (Ideal.subset_span (by simp))
  have hy : 1 - x ∈ Ideal.span {x, y} ⊔ Ideal.span {1 - x, z} :=
    Ideal.mem_sup_right (Ideal.subset_span (by simp))
  simpa using Ideal.add_mem _ hx hy

private theorem span_pair_one_sub_mul_sup (x y c : PairPolynomial R) :
    Ideal.span {y - x, 1 - c * x} ⊔ Ideal.span {x, y} = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have hx : x ∈ Ideal.span {y - x, 1 - c * x} ⊔ Ideal.span {x, y} :=
    Ideal.mem_sup_right (Ideal.subset_span (by simp))
  have hy : 1 - c * x ∈ Ideal.span {y - x, 1 - c * x} ⊔ Ideal.span {x, y} :=
    Ideal.mem_sup_left (Ideal.subset_span (by simp))
  simpa using Ideal.add_mem _ hy (Ideal.mul_mem_left _ c hx)

private theorem centre_ideals_0 (t : R) :
    normalizedCentreIdeal R t 0 = ![Ideal.span {X 0, X 1}, ⊤, Ideal.span {X 0 - 1, X 1 - C t}, ⊤] := by
  funext r
  fin_cases r <;>
    simp [normalizedCentreIdeal, normalizedPair, normalizedVector, pairIdeal,
      Ideal.span_insert, Ideal.span_singleton_one]

private theorem centre_pairwise_0 (t : R) (r s : Fin 4) (hrs : r ≠ s) :
    normalizedCentreIdeal R t 0 r ⊔ normalizedCentreIdeal R t 0 s = ⊤ := by
  rw [centre_ideals_0]
  fin_cases r <;> fin_cases s <;> simp at hrs ⊢
  all_goals first
    | exact span_pair_sub_one_sup R (X 0) (X 1) (X 1 - C t)
    | simpa only [sup_comm] using span_pair_sub_one_sup R (X 0) (X 1) (X 1 - C t)

private theorem centre_ideals_1 (t : R) :
    normalizedCentreIdeal R t 1 = ![⊤, Ideal.span {X 0, X 1}, Ideal.span {1 - X 0, X 1 - C t * X 0}, ⊤] := by
  funext r
  fin_cases r <;>
    simp [normalizedCentreIdeal, normalizedPair, normalizedVector, pairIdeal,
      Ideal.span_insert, Ideal.span_singleton_one]

private theorem centre_pairwise_1 (t : R) (r s : Fin 4) (hrs : r ≠ s) :
    normalizedCentreIdeal R t 1 r ⊔ normalizedCentreIdeal R t 1 s = ⊤ := by
  rw [centre_ideals_1]
  fin_cases r <;> fin_cases s <;> simp at hrs ⊢
  all_goals first
    | exact span_pair_one_sub_sup R (X 0) (X 1) (X 1 - C t * X 0)
    | simpa only [sup_comm] using span_pair_one_sub_sup R (X 0) (X 1) (X 1 - C t * X 0)

private theorem centre_ideals_2 (t : R) :
    normalizedCentreIdeal R t 2 = ![⊤, ⊤, Ideal.span {X 1 - X 0, 1 - C t * X 0}, Ideal.span {X 0, X 1}] := by
  funext r
  fin_cases r <;>
    simp [normalizedCentreIdeal, normalizedPair, normalizedVector, pairIdeal,
      Ideal.span_insert, Ideal.span_singleton_one]

private theorem centre_pairwise_2 (t : R) (r s : Fin 4) (hrs : r ≠ s) :
    normalizedCentreIdeal R t 2 r ⊔ normalizedCentreIdeal R t 2 s = ⊤ := by
  rw [centre_ideals_2]
  fin_cases r <;> fin_cases s <;> simp at hrs ⊢
  all_goals first
    | exact span_pair_one_sub_mul_sup R (X 0) (X 1) (C t)
    | simpa only [sup_comm] using span_pair_one_sub_mul_sup R (X 0) (X 1) (C t)

/-- Distinct centre ideals are comaximal on every normalized affine base chart. -/
theorem normalizedCentreIdeal_pairwise (t : R) (a : Fin 3) (r s : Fin 4) (hrs : r ≠ s) :
    normalizedCentreIdeal R t a r ⊔ normalizedCentreIdeal R t a s = ⊤ := by
  fin_cases a
  · exact centre_pairwise_0 R t r s hrs
  · exact centre_pairwise_1 R t r s hrs
  · exact centre_pairwise_2 R t r s hrs

/-- The comaximality identity excludes simultaneous containment at every prime. -/
theorem normalizedCentres_not_both (t : R) (a : Fin 3)
    (p : PrimeSpectrum (PairPolynomial R)) (r s : Fin 4) (hrs : r ≠ s)
    (hr : normalizedCentreIdeal R t a r ≤ p.asIdeal) :
    ¬ normalizedCentreIdeal R t a s ≤ p.asIdeal := by
  intro hs
  have h := sup_le hr hs
  rw [normalizedCentreIdeal_pairwise R t a r s hrs] at h
  exact p.isPrime.ne_top (top_le_iff.mp h)

/-- All scheme points admit a neighbourhood avoiding the other three centres;
this is the ideal-theoretic point-cover assertion, before constructing opens. -/
theorem normalizedCentres_prime_cover (t : R) (a : Fin 3)
    (p : PrimeSpectrum (PairPolynomial R)) :
    ∃ r : Fin 4, ∀ s : Fin 4, s ≠ r → ¬ normalizedCentreIdeal R t a s ≤ p.asIdeal := by
  classical
  by_cases h : ∃ r : Fin 4, normalizedCentreIdeal R t a r ≤ p.asIdeal
  · obtain ⟨r, hr⟩ := h
    exact ⟨r, fun s hs => normalizedCentres_not_both R t a p r s (Ne.symm hs) hr⟩
  · exact ⟨0, fun s _ hs => h ⟨s, hs⟩⟩

end
end FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate
