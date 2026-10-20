import FailureOfSemipositiveMetricExtension.CoordinateBlowupOfficial.PreferredIncidenceCover

/-! Exact ideal pullback on the four preferred principal opens of the fixed
unreduced four-centre incidence chart. The original centre is the INTERSECTION
of the four concrete affine centre ideals. No radical, closed-point test,
normalization equivalence, or literature theorem is assumed. -/
namespace FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate
noncomputable section
open MvPolynomial
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R]

/-- The fixed direction relation, in the actual unreduced quotient ring. -/
theorem slope_selected_relation (t : R) (a : Fin 3) (e : Fin 4 → Fin 2) (r : Fin 4) :
    algebraMap (PairPolynomial R) (SlopeRing R t a e) (normalizedPair R t a r (e r)) *
      Ideal.Quotient.mk _ (X r) =
    algebraMap (PairPolynomial R) (SlopeRing R t a e) (normalizedPair R t a r (e r).rev) := by
  apply sub_eq_zero.mp
  exact slope_relation_zero R t a e r

/-- Each concrete centre ideal has the selected equation as generator after
pullback to this incidence chart, including on its exceptional locus. -/
theorem slope_centreIdeal_principal (t : R) (a : Fin 3) (e : Fin 4 → Fin 2) (r : Fin 4) :
    (normalizedCentreIdeal R t a r).map (algebraMap (PairPolynomial R) (SlopeRing R t a e)) =
      Ideal.span {algebraMap (PairPolynomial R) (SlopeRing R t a e)
        (normalizedPair R t a r (e r))} := by
  let f := algebraMap (PairPolynomial R) (SlopeRing R t a e)
  have hmem (b : Fin 2) : f (normalizedPair R t a r b) ∈
      Ideal.span {f (normalizedPair R t a r (e r))} := by
    by_cases hb : b = e r
    · rw [hb]; exact Ideal.subset_span (Set.mem_singleton _)
    · have hb' : b = (e r).rev := by
        generalize e r = c at hb ⊢
        fin_cases b <;> fin_cases c <;> simp_all
      rw [hb', ← slope_selected_relation]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap, normalizedCentreIdeal, pairIdeal, Ideal.span_le]
    rintro x (rfl | rfl) <;> exact hmem _
  · apply Ideal.span_le.mpr
    rintro x rfl
    exact Ideal.mem_map_of_mem _ (normalizedPair_mem R t a r (e r))

abbrev PreferredIncidenceRing (t : R) (a : Fin 3) (e : Fin 4 → Fin 2) (r : Fin 4) :=
  Localization.Away (preferredIncidenceDenominator R t a e r)

def preferredIncidenceBaseHom (t : R) (a : Fin 3) (e : Fin 4 → Fin 2) (r : Fin 4) :
    PairPolynomial R →+* PreferredIncidenceRing R t a e r :=
  (algebraMap (SlopeRing R t a e) (PreferredIncidenceRing R t a e r)).comp
    (algebraMap (PairPolynomial R) (SlopeRing R t a e))

/-- The preferred projective normalization is genuinely valid on this open. -/
theorem preferredIncidence_base_pivot_unit (t : R) (a : Fin 3) (e : Fin 4 → Fin 2) (r : Fin 4) :
    IsUnit (preferredIncidenceBaseHom R t a e r
      (normalizedVector R a (preferredCentreChart r))) := by
  apply IsLocalization.Away.isUnit_of_dvd (preferredIncidenceDenominator R t a e r)
  rw [preferredIncidenceDenominator, map_mul]
  exact dvd_mul_right _ _

theorem preferredIncidence_other_selected_unit (t : R) (a : Fin 3) (e : Fin 4 → Fin 2)
    (r s : Fin 4) (hs : s ≠ r) :
    IsUnit (preferredIncidenceBaseHom R t a e r (normalizedPair R t a s (e s))) := by
  apply IsLocalization.Away.isUnit_of_dvd (preferredIncidenceDenominator R t a e r)
  apply map_dvd
  apply dvd_mul_of_dvd_right
  exact Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hs, Finset.mem_univ s⟩)

theorem preferredIncidence_other_ideal_top (t : R) (a : Fin 3) (e : Fin 4 → Fin 2)
    (r s : Fin 4) (hs : s ≠ r) :
    (normalizedCentreIdeal R t a s).map (preferredIncidenceBaseHom R t a e r) = ⊤ := by
  exact Ideal.eq_top_of_isUnit_mem _
    (Ideal.mem_map_of_mem _ (normalizedPair_mem R t a s (e s)))
    (preferredIncidence_other_selected_unit R t a e r s hs)

theorem preferredIncidence_retained_ideal_principal (t : R) (a : Fin 3)
    (e : Fin 4 → Fin 2) (r : Fin 4) :
    (normalizedCentreIdeal R t a r).map (preferredIncidenceBaseHom R t a e r) =
      Ideal.span {preferredIncidenceBaseHom R t a e r (normalizedPair R t a r (e r))} := by
  rw [preferredIncidenceBaseHom, ← Ideal.map_map, slope_centreIdeal_principal,
    Ideal.map_span, Set.image_singleton]
  rfl

/-- The actual scheme-theoretic union of the four centres on the affine base. -/
def totalCentreIdeal (t : R) (a : Fin 3) : Ideal (PairPolynomial R) :=
  ⨅ s : Fin 4, normalizedCentreIdeal R t a s

/-- Exact equality of extended ideals, not just equality of supports. In
particular, no flatness of the incidence projection has been smuggled in. -/
theorem preferredIncidence_total_centre_principal (t : R) (a : Fin 3)
    (e : Fin 4 → Fin 2) (r : Fin 4) :
    (totalCentreIdeal R t a).map (preferredIncidenceBaseHom R t a e r) =
      Ideal.span {preferredIncidenceBaseHom R t a e r (normalizedPair R t a r (e r))} := by
  classical
  let f := preferredIncidenceBaseHom R t a e r
  have hprod : (∏ s : Fin 4, normalizedCentreIdeal R t a s).map f =
      (normalizedCentreIdeal R t a r).map f := by
    change Ideal.mapHom f (∏ s : Fin 4, normalizedCentreIdeal R t a s) = _
    rw [map_prod]
    apply Finset.prod_eq_single r
    · intro s _ hs
      exact (preferredIncidence_other_ideal_top R t a e r s hs).trans Ideal.one_eq_top.symm
    · simp
  have hlo : (∏ s : Fin 4, normalizedCentreIdeal R t a s) ≤ totalCentreIdeal R t a := by
    simpa only [Finset.inf_univ_eq_iInf] using
      (Ideal.prod_le_inf (s := Finset.univ) (f := normalizedCentreIdeal R t a))
  rw [← preferredIncidence_retained_ideal_principal R t a e r]
  apply le_antisymm
  · exact Ideal.map_mono (iInf_le _ r)
  · rw [← hprod]
    exact Ideal.map_mono hlo

/-- Four opens cover every scheme point, and on each the exact total-centre
pullback has the displayed single generator. Regularity of that generator and
identification with coordinate Rees charts are separate remaining obligations. -/
theorem four_preferred_opens_with_principal_total_centre (t : R) (a : Fin 3)
    (e : Fin 4 → Fin 2) (p : PrimeSpectrum (SlopeRing R t a e)) :
    ∃ r : Fin 4, p ∈ PrimeSpectrum.basicOpen (preferredIncidenceDenominator R t a e r) ∧
      IsUnit (preferredIncidenceBaseHom R t a e r
        (normalizedVector R a (preferredCentreChart r))) ∧
      (totalCentreIdeal R t a).map (preferredIncidenceBaseHom R t a e r) =
        Ideal.span {preferredIncidenceBaseHom R t a e r (normalizedPair R t a r (e r))} := by
  obtain ⟨r,hr⟩ := preferredIncidence_principal_open_cover R t a e p
  exact ⟨r,hr,preferredIncidence_base_pivot_unit R t a e r,
    preferredIncidence_total_centre_principal R t a e r⟩

end
end FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate
