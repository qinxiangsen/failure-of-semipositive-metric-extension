import FailureOfSemipositiveMetricExtension.ProjectivePlaneAtlas

/-! Hausdorffness of the actual complex projective-plane quotient with its constructed
standard atlas. The proof separates common-chart pairs by open embeddings and remaining
pairs by small cross-coordinate neighbourhoods. -/

noncomputable section

namespace FailureOfSemipositiveMetricExtension.ProjectivePlane

open Set Topology

/-- Every normalized homogeneous component is continuous in affine coordinates. -/
theorem vector_component_continuous (i j : Fin 3) :
    Continuous (fun q : ℂ × ℂ => vector i q j) := by
  fin_cases i <;> fin_cases j <;> simp [vector] <;> fun_prop

private def Separated (p p' : Point) : Prop :=
  ∃ U V : Set Point, IsOpen U ∧ IsOpen V ∧ p ∈ U ∧ p' ∈ V ∧ Disjoint U V

private theorem separate_same_chart (i : Fin 3) (q q' : ℂ × ℂ)
    (h : param i q ≠ param i q') : Separated (param i q) (param i q') := by
  apply separated_by_isOpenEmbedding (x := q) (y := q') (param_isOpenEmbedding i)
  intro heq
  exact h (congrArg (param i) heq)

/-- Small cross-coordinate regions in opposite charts cannot meet. -/
theorem small_cross_coordinate_images_disjoint (i j : Fin 3) :
    Disjoint (param i '' {q | ‖vector i q j‖ < 1})
      (param j '' {q | ‖vector j q i‖ < 1}) := by
  rw [Set.disjoint_left]
  rintro p ⟨q,hq,hqp⟩ ⟨q',hq',hq'p⟩
  have hprod := cross_ratio_eq_one i j q q' (hqp.trans hq'p.symm)
  have hnorm : ‖vector i q j‖ * ‖vector j q' i‖ = 1 := by
    rw [← norm_mul,hprod,norm_one]
  have hlt : ‖vector i q j‖ * ‖vector j q' i‖ < 1 := calc
    _ ≤ 1 * ‖vector j q' i‖ := mul_le_mul_of_nonneg_right (le_of_lt hq) (norm_nonneg _)
    _ < 1 := by simpa using hq'
  exact (ne_of_lt hlt) hnorm

private theorem separate_zero_cross_coordinates (i j : Fin 3) (q q' : ℂ × ℂ)
    (hq : vector i q j = 0) (hq' : vector j q' i = 0) :
    Separated (param i q) (param j q') := by
  have hU : IsOpen {q : ℂ × ℂ | ‖vector i q j‖ < 1} :=
    isOpen_lt (vector_component_continuous i j).norm continuous_const
  have hV : IsOpen {q : ℂ × ℂ | ‖vector j q i‖ < 1} :=
    isOpen_lt (vector_component_continuous j i).norm continuous_const
  exact ⟨_,_,(param_isOpenEmbedding i).isOpenMap _ hU,
    (param_isOpenEmbedding j).isOpenMap _ hV,
    ⟨q,by simp [hq],rfl⟩,⟨q',by simp [hq'],rfl⟩,
    small_cross_coordinate_images_disjoint i j⟩

/-- Arbitrary distinct projective points admit disjoint open neighbourhoods. -/
theorem points_separated (p p' : Point) (hpp' : p ≠ p') :
    ∃ U V : Set Point, IsOpen U ∧ IsOpen V ∧ p ∈ U ∧ p' ∈ V ∧ Disjoint U V := by
  obtain ⟨i,q,rfl⟩ := charts_cover p
  obtain ⟨j,q',rfl⟩ := charts_cover p'
  by_cases hq : vector i q j = 0
  · by_cases hq' : vector j q' i = 0
    · exact separate_zero_cross_coordinates i j q q' hq hq'
    · rw [param_transition j i q' hq'] at hpp' ⊢
      exact separate_same_chart i _ _ hpp'
  · rw [param_transition i j q hq] at hpp' ⊢
    exact separate_same_chart j _ _ hpp'

/-- Hausdorffness is proved separately from the analytic chart-compatibility instance. -/
instance instT2SpacePoint : T2Space Point where
  t2 := points_separated

end FailureOfSemipositiveMetricExtension.ProjectivePlane
