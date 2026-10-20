import FailureOfSemipositiveMetricExtension.GlobalExceptionalOrder

/-! A genuine common refinement of the eight blow-up charts and actual bundle frames. -/
namespace FailureOfSemipositiveMetricExtension.GlobalLineBundle
noncomputable section
open Set FailureOfSemipositiveMetricExtension.GlobalIncidence
attribute [local instance] Classical.propDecidable

abbrev DivisionIndex := Fin 4 × Fin 2 × (Fin 4 → Fin 2)

def divisionFrame (k : DivisionIndex) : Index :=
  (baseChart k.1,Function.update k.2.2 k.1 k.2.1)

def divisionPatch (k : DivisionIndex) : Set Total :=
  chartSource k.1 k.2.1 ∩ baseSet (divisionFrame k)

theorem divisionFrame_selected (k : DivisionIndex) : (divisionFrame k).2 k.1 = k.2.1 := by
  simp [divisionFrame]

theorem divisionPatch_isOpen (k : DivisionIndex) : IsOpen (divisionPatch k) :=
  (chartSource_isOpen _ _).inter (baseSet_isOpen _)

theorem divisionPatch_cover (p : Total) : ∃ k, p ∈ divisionPatch k := by
  obtain ⟨r,e,q,hq,hp⟩ := global_charts_cover p
  let b := ((core 0 (fun _ => 0)).indexAt p).2
  refine ⟨(r,e,b),⟨q,hq,hp.symm⟩,?_,?_⟩
  · rw [hp]
    exact affineBase_mem_chartSet r q.2 _
  · intro j
    by_cases hj : j = r
    · subst j
      change directions p r ∈ FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet (Function.update b r e r)
      rw [Function.update_self,hp]
      rw [chartParam,localLift_direction,localParam_direction]
      exact ⟨q.1.2,rfl⟩
    · have hm := ((core 0 (fun _ => 0)).mem_baseSet_at p).2 j
      simpa [divisionFrame,Function.update_of_ne hj,b] using hm

theorem divisionPatch_subset_frame (k : DivisionIndex) : divisionPatch k ⊆ baseSet (divisionFrame k) :=
  inter_subset_right

theorem divisionPatch_avoids_other_centres (k : DivisionIndex) (p : Total)
    (hp : p ∈ divisionPatch k) (j : Fin 4) (hj : j ≠ k.1) :
    blowdown p ≠ centre j (projection p) :=
  ((mem_chartSource_iff k.1 k.2.1 p).mp hp.1).2.2 j hj
end
end FailureOfSemipositiveMetricExtension.GlobalLineBundle
