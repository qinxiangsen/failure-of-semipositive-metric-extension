import FailureOfSemipositiveMetricExtension.PaperStrictTransformCertificate

/-! The three named Q lines are distinct as actual projective subsets, with
explicit separating points outside all four central centres. This is the
remaining instance premise for the standard reduced strict-transform divisor
sum interpretation; no irreducibility or divisor theory is axiomatized. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.PaperStrictTransforms
noncomputable section
open Set

def separatingCoordinates : Fin 3 → ℂ × ℂ := ![(1,0),(0,1),(1,1)]

def separatingPoint (k : Fin 3) : PlanePoint :=
  ProjectivePlane.param 2 (separatingCoordinates k)

/-- [1:0:1], [0:1:1], [1:1:1] lie respectively on exactly one named Q line. -/
theorem separatingPoint_on_line_iff (k j : Fin 3) :
    separatingPoint k ∈ lineZero (qForm j) ↔ k = j := by
  change Projectivization.mk ℂ _ _ ∈ lineZero (qForm j) ↔ _
  rw [lineZero_mk]
  fin_cases k <;> fin_cases j <;>
    norm_num [qForm,separatingCoordinates,ProjectivePlane.vector]

theorem separatingPoint_avoids_all_centres (k : Fin 3) (r : Fin 4) :
    separatingPoint k ≠ centre r 0 := by
  intro h
  have hm : ProjectivePlane.vector 2 (separatingCoordinates k) ∈ (centre r 0).submodule :=
    (projective_eq_iff_mem _ (ProjectivePlane.vector_nonzero 2 (separatingCoordinates k)) _).mp h
  have hz := (pairMap_zero_iff_mem_centre r 0 _).mpr hm
  fin_cases k <;> fin_cases r <;>
    norm_num [pairMap,pair,separatingCoordinates,ProjectivePlane.vector,Matrix.cons_val_two] at hz

theorem named_projective_line_sets_pairwise_distinct :
    Pairwise (fun i j : Fin 3 => lineZero (qForm i) ≠ lineZero (qForm j)) := by
  intro i j hij heq
  have hi : separatingPoint i ∈ lineZero (qForm i) :=
    (separatingPoint_on_line_iff i i).mpr rfl
  rw [heq] at hi
  exact hij ((separatingPoint_on_line_iff i j).mp hi)

/-- Concrete nonempty line pieces remain distinct after removal of the four
centres, which is the exact open set used in the literal closure definition. -/
theorem separated_off_centre_line_pieces :
    ∀ i : Fin 3, ∃ p : PlanePoint,
      (∀ r : Fin 4, p ≠ centre r 0) ∧
      p ∈ lineZero (qForm i) ∧
      ∀ j : Fin 3, j ≠ i → p ∉ lineZero (qForm j) := by
  intro i
  refine ⟨separatingPoint i,separatingPoint_avoids_all_centres i,
    (separatingPoint_on_line_iff i i).mpr rfl,?_⟩
  intro j hji hp
  exact hji ((separatingPoint_on_line_iff i j).mp hp).symm

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.PaperStrictTransforms
