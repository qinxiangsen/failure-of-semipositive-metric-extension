import FailureOfSemipositiveMetricExtension.ProjectivePlaneSeparation
import Mathlib.Data.Finset.Max

/-!
Compactness of the actual complex projective plane with its constructed affine-atlas
 topology. A maximal homogeneous coordinate puts each point in a closed unit polydisc
 in one of the three standard affine charts. These three compact images cover the plane.
-/

noncomputable section

namespace FailureOfSemipositiveMetricExtension.ProjectivePlane

open Set

/-- A nonzero homogeneous vector has a nonzero coordinate of maximal norm. -/
theorem exists_max_norm_coordinate (v : Fin 3 → ℂ) (hv : v ≠ 0) :
    ∃ i, v i ≠ 0 ∧ ∀ j, ‖v j‖ ≤ ‖v i‖ := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖v i‖)
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin 3)).Nonempty)
  have hmax : ∀ j, ‖v j‖ ≤ ‖v i‖ := fun j => hi j (Finset.mem_univ j)
  refine ⟨i, ?_, hmax⟩
  intro hzero
  apply hv
  ext j
  apply norm_eq_zero.mp
  exact le_antisymm (by simpa [hzero] using hmax j) (norm_nonneg _)

/-- Dividing by a maximal coordinate bounds both normalized affine coordinates by one. -/
theorem normalize_norm_le_one (i : Fin 3) (v : Fin 3 → ℂ) (hi : v i ≠ 0)
    (hmax : ∀ j, ‖v j‖ ≤ ‖v i‖) :
    ‖(normalize i v).1‖ ≤ 1 ∧ ‖(normalize i v).2‖ ≤ 1 := by
  have hdiv : ∀ j, ‖v j / v i‖ ≤ 1 := by
    intro j
    rw [norm_div]
    exact (div_le_one (norm_pos_iff.mpr hi)).mpr (hmax j)
  fin_cases i
  · exact ⟨hdiv 1, hdiv 2⟩
  · exact ⟨hdiv 0, hdiv 2⟩
  · exact ⟨hdiv 0, hdiv 1⟩

/-- The three closed unit polydiscs in standard affine charts cover projective space. -/
theorem bounded_charts_cover (p : Point) :
    ∃ i q, p = param i q ∧ ‖q.1‖ ≤ 1 ∧ ‖q.2‖ ≤ 1 := by
  induction p using Projectivization.ind with
  | h v hv =>
    obtain ⟨i, hi, hmax⟩ := exists_max_norm_coordinate v hv
    refine ⟨i, normalize i v, ?_, normalize_norm_le_one i v hi hmax⟩
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    exact ⟨v i, vector_normalize i v hi⟩

/-- The compact affine coordinate domain used for the finite covering. -/
def unitPolydisc : Set (ℂ × ℂ) := {q | ‖q.1‖ ≤ 1 ∧ ‖q.2‖ ≤ 1}

theorem unitPolydisc_eq_prod_closedBall :
    unitPolydisc = Metric.closedBall (0 : ℂ) 1 ×ˢ Metric.closedBall (0 : ℂ) 1 := by
  ext q
  simp [unitPolydisc, Metric.mem_closedBall, dist_zero_right]

theorem unitPolydisc_isCompact : IsCompact unitPolydisc := by
  rw [unitPolydisc_eq_prod_closedBall]
  exact (isCompact_closedBall (0 : ℂ) 1).prod (isCompact_closedBall (0 : ℂ) 1)

/-- Each closed-polydisc chart image is a compact subset of the actual projective plane. -/
theorem param_unitPolydisc_isCompact (i : Fin 3) :
    IsCompact (param i '' unitPolydisc) :=
  unitPolydisc_isCompact.image (param_continuous i)

/-- A concrete finite compact covering by the three standard chart images. -/
theorem iUnion_param_unitPolydisc :
    (⋃ i : Fin 3, param i '' unitPolydisc) = (Set.univ : Set Point) := by
  apply Set.eq_univ_of_forall
  intro p
  obtain ⟨i, q, hp, hq⟩ := bounded_charts_cover p
  exact Set.mem_iUnion.mpr ⟨i, q, hq, hp.symm⟩

/-- Global compactness follows from the explicit finite compact chart covering. -/
theorem projectivePlane_isCompact : IsCompact (Set.univ : Set Point) := by
  rw [← iUnion_param_unitPolydisc]
  exact isCompact_iUnion param_unitPolydisc_isCompact

instance instCompactSpacePoint : CompactSpace Point := ⟨projectivePlane_isCompact⟩

end FailureOfSemipositiveMetricExtension.ProjectivePlane
