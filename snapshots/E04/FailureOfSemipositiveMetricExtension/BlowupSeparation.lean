import FailureOfSemipositiveMetricExtension.BlowupAtlas

/-!
Hausdorff separation for the actual two-chart incidence blow-up. Points in a common
affine chart are separated by its open embedding. The remaining pairs lie on opposite
coordinate directions and are separated by the images of the strict unit slope discs.
-/

noncomputable section

namespace FailureOfSemipositiveMetricExtension.Blowup

open Set Topology

private def Separated (p q : Point) : Prop :=
  ∃ U V : Set Point, IsOpen U ∧ IsOpen V ∧ p ∈ U ∧ q ∈ V ∧ Disjoint U V

private theorem separate_X_X (r s u v : ℂ) (h : X r s ≠ X u v) :
    Separated (X r s) (X u v) := by
  apply separated_by_isOpenEmbedding (x := (r,s)) (y := (u,v)) X_isOpenEmbedding
  intro heq
  exact h (congrArg (fun q : ℂ × ℂ => X q.1 q.2) heq)

private theorem separate_Y_Y (r s u v : ℂ) (h : Y r s ≠ Y u v) :
    Separated (Y r s) (Y u v) := by
  apply separated_by_isOpenEmbedding (x := (r,s)) (y := (u,v)) Y_isOpenEmbedding
  intro heq
  exact h (congrArg (fun q : ℂ × ℂ => Y q.1 q.2) heq)

/-- The two small-slope chart regions are disjoint because overlap slopes multiply to one. -/
theorem small_slope_images_disjoint :
    Disjoint ((fun q : ℂ × ℂ => X q.1 q.2) '' {q | ‖q.2‖ < 1})
      ((fun q : ℂ × ℂ => Y q.1 q.2) '' {q | ‖q.2‖ < 1}) := by
  rw [Set.disjoint_left]
  rintro p ⟨a,ha,hap⟩ ⟨b,hb,hbp⟩
  have hprod : a.2*b.2 = 1 :=
    ((X_eq_Y_iff a.1 a.2 b.1 b.2).mp (hap.trans hbp.symm)).2
  have hnorm : ‖a.2‖ * ‖b.2‖ = 1 := by rw [← norm_mul,hprod,norm_one]
  have hlt : ‖a.2‖ * ‖b.2‖ < 1 := calc
    _ ≤ 1 * ‖b.2‖ := mul_le_mul_of_nonneg_right (le_of_lt ha) (norm_nonneg _)
    _ < 1 := by simpa using hb
  exact (ne_of_lt hlt) hnorm

private theorem separate_opposite_axes (r u : ℂ) : Separated (X r 0) (Y u 0) := by
  let D : Set (ℂ × ℂ) := {q | ‖q.2‖ < 1}
  have hD : IsOpen D := isOpen_lt continuous_snd.norm continuous_const
  refine ⟨(fun q : ℂ × ℂ => X q.1 q.2) '' D,
    (fun q : ℂ × ℂ => Y q.1 q.2) '' D,
    X_isOpenEmbedding.isOpenMap _ hD, Y_isOpenEmbedding.isOpenMap _ hD,
    ⟨(r,0),?_,rfl⟩,⟨(u,0),?_,rfl⟩,small_slope_images_disjoint⟩ <;> simp [D]

private theorem separate_X_Y (r s u v : ℂ) (h : X r s ≠ Y u v) :
    Separated (X r s) (Y u v) := by
  by_cases hs : s = 0
  · subst s
    by_cases hv : v = 0
    · subst v
      exact separate_opposite_axes r u
    · rw [Y_eq_X_transition u v hv] at h ⊢
      exact separate_X_X _ _ _ _ h
  · rw [X_eq_Y_transition r s hs] at h ⊢
    exact separate_Y_Y _ _ _ _ h

/-- Every distinct pair has explicitly proved disjoint open neighbourhoods. -/
theorem points_separated (p q : Point) (hpq : p ≠ q) :
    ∃ U V : Set Point, IsOpen U ∧ IsOpen V ∧ p ∈ U ∧ q ∈ V ∧ Disjoint U V := by
  rcases charts_cover p with ⟨r,s,rfl⟩ | ⟨r,s,rfl⟩ <;>
    rcases charts_cover q with ⟨u,v,rfl⟩ | ⟨u,v,rfl⟩
  · exact separate_X_X r s u v hpq
  · exact separate_X_Y r s u v hpq
  · obtain ⟨U,V,hU,hV,hp,hq,hUV⟩ := separate_X_Y u v r s hpq.symm
    exact ⟨V,U,hV,hU,hq,hp,hUV.symm⟩
  · exact separate_Y_Y r s u v hpq

/-- The affine blow-up is Hausdorff; this is independent of manifold compatibility. -/
instance instT2SpacePoint : T2Space Point where
  t2 := points_separated

end FailureOfSemipositiveMetricExtension.Blowup
