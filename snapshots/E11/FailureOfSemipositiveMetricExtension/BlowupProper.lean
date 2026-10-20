import FailureOfSemipositiveMetricExtension.BlowupSeparation
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import FailureOfSemipositiveMetricExtension.Topology

/-!
Properness of the actual affine blow-down. Every direction is covered by one of
the two closed unit slope discs. Above a compact base set the radial coordinate is
bounded, so its inverse image is a closed subset of two compact chart images.
-/

noncomputable section

namespace FailureOfSemipositiveMetricExtension.Blowup

open Set Metric

/-- Closed unit slope discs in the two affine charts already cover the blow-up. -/
theorem charts_cover_boundedSlope (p : Point) :
    (∃ r s, p = X r s ∧ ‖s‖ ≤ 1) ∨ (∃ r s, p = Y r s ∧ ‖s‖ ≤ 1) := by
  have hinv : ∀ s : ℂ, ¬ ‖s‖ ≤ 1 → s ≠ 0 ∧ ‖s⁻¹‖ ≤ 1 := by
    intro s hs
    have hlarge : 1 < ‖s‖ := lt_of_not_ge hs
    have hpos : 0 < ‖s‖ := zero_lt_one.trans hlarge
    refine ⟨norm_pos_iff.mp hpos,?_⟩
    rw [norm_inv]
    exact (inv_le_one₀ hpos).mpr hlarge.le
  rcases charts_cover p with ⟨r,s,rfl⟩ | ⟨r,s,rfl⟩
  · by_cases hs : ‖s‖ ≤ 1
    · exact Or.inl ⟨r,s,rfl,hs⟩
    · have hi := hinv s hs
      exact Or.inr ⟨r*s,s⁻¹,X_eq_Y_transition r s hi.1,hi.2⟩
  · by_cases hs : ‖s‖ ≤ 1
    · exact Or.inr ⟨r,s,rfl,hs⟩
    · have hi := hinv s hs
      exact Or.inl ⟨r*s,s⁻¹,Y_eq_X_transition r s hi.1,hi.2⟩

/-- Compact coordinate sets used to bound inverse images of compact affine base sets. -/
def closedPolydisc (R : ℝ) : Set (ℂ × ℂ) :=
  closedBall 0 R ×ˢ closedBall 0 1

theorem closedPolydisc_isCompact (R : ℝ) : IsCompact (closedPolydisc R) :=
  (isCompact_closedBall (0 : ℂ) R).prod (isCompact_closedBall (0 : ℂ) 1)

/-- The inverse image of every compact set in the affine plane is compact. -/
theorem projection_preimage_isCompact {K : Set Plane} (hK : IsCompact K) :
    IsCompact (projection ⁻¹' K) := by
  obtain ⟨R,hR⟩ := hK.isBounded.exists_norm_le
  have hcX := (closedPolydisc_isCompact R).image X_continuous
  have hcY := (closedPolydisc_isCompact R).image Y_continuous
  apply (hcX.union hcY).of_isClosed_subset (hK.isClosed.preimage projection_continuous)
  intro p hp
  rcases charts_cover_boundedSlope p with ⟨r,s,rfl,hs⟩ | ⟨r,s,rfl,hs⟩
  · have hr : ‖r‖ ≤ R := calc
      _ = ‖projection (X r s) 0‖ := by simp
      _ ≤ ‖projection (X r s)‖ := norm_le_pi_norm _ 0
      _ ≤ R := hR _ hp
    left
    refine ⟨(r,s),?_,rfl⟩
    simpa [closedPolydisc,mem_closedBall,dist_zero_right] using And.intro hr hs
  · have hr : ‖r‖ ≤ R := calc
      _ = ‖projection (Y r s) 1‖ := by simp
      _ ≤ ‖projection (Y r s)‖ := norm_le_pi_norm _ 1
      _ ≤ R := hR _ hp
    right
    refine ⟨(r,s),?_,rfl⟩
    simpa [closedPolydisc,mem_closedBall,dist_zero_right] using And.intro hr hs

/-- The blow-down of the constructed affine blow-up is a genuine proper map. -/
theorem projection_isProperMap : IsProperMap projection :=
  isProperMap_iff_isCompact_preimage.mpr
    ⟨projection_continuous,fun _ hK => projection_preimage_isCompact hK⟩

theorem projection_isClosedMap : IsClosedMap projection := projection_isProperMap.isClosedMap

/-- In particular the actual exceptional fibre is compact. -/
theorem exceptional_isCompact : IsCompact {p : Point | projection p = 0} :=
  projection_isProperMap.isCompact_preimage isCompact_singleton

/-- Every open neighbourhood of a fibre contains the inverse image of a base neighbourhood. -/
theorem fiber_neighborhood (b : Plane) (U : Set Point) (hU : IsOpen U)
    (hfiber : projection ⁻¹' {b} ⊆ U) :
    ∃ V : Set Plane, IsOpen V ∧ b ∈ V ∧ projection ⁻¹' V ⊆ U :=
  FailureOfSemipositiveMetricExtension.proper_fiber_neighborhood projection projection_isProperMap b U hU hfiber

end FailureOfSemipositiveMetricExtension.Blowup
