import Mathlib.Topology.Semicontinuous
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic

namespace FailureOfSemipositiveMetricExtension
open Set

/-- An upper-semicontinuous function on a compact space, allowed to take -∞
but not +∞, has a finite real upper bound. This is the topological step used
for a global quasi-psh potential; the quasi-psh representative is not constructed here. -/
theorem usc_withBot_bounded_above {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (u : X → WithBot ℝ) (hu : UpperSemicontinuous u) :
    ∃ C : ℝ, ∀ x, u x ≤ (C : WithBot ℝ) := by
  classical
  let U : ℝ → Set X := fun c => u ⁻¹' Iio (c : WithBot ℝ)
  have hU : ∀ c, IsOpen (U c) := fun c => hu.isOpen_preimage c
  have hcover : (univ : Set X) ⊆ ⋃ c, U c := by
    intro x _
    apply mem_iUnion.mpr
    cases hux : u x with
    | bot =>
        refine ⟨0, ?_⟩
        change u x < ((0 : ℝ) : WithBot ℝ)
        rw [hux]
        exact WithBot.bot_lt_coe 0
    | coe r =>
        refine ⟨r+1, ?_⟩
        change u x < ((r+1 : ℝ) : WithBot ℝ)
        rw [hux]
        exact WithBot.coe_lt_coe.mpr (by linarith)
  rcases isCompact_univ.elim_finite_subcover U hU hcover with ⟨s,hs⟩
  refine ⟨∑ c ∈ s, |c|, ?_⟩
  intro x
  rcases mem_iUnion.mp (hs (mem_univ x)) with ⟨c,hc⟩
  rcases mem_iUnion.mp hc with ⟨hcs,hxc⟩
  have hbound : c ≤ ∑ a ∈ s, |a| :=
    (le_abs_self c).trans (Finset.single_le_sum (fun a _ => abs_nonneg a) hcs)
  exact le_trans (le_of_lt hxc) (WithBot.coe_le_coe.mpr hbound)
end FailureOfSemipositiveMetricExtension
