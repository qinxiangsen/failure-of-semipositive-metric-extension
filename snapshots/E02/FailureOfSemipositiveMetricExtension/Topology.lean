import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic

namespace FailureOfSemipositiveMetricExtension
open Set

/-- Properness gives an entire inverse-image neighbourhood inside any open
neighbourhood of one fibre. This proves the exact topological shrinking step. -/
theorem proper_fiber_neighborhood {X B : Type*} [TopologicalSpace X]
    [TopologicalSpace B] (π : X → B) (hπ : IsProperMap π)
    (b : B) (U : Set X) (hU : IsOpen U) (hfiber : π ⁻¹' {b} ⊆ U) :
    ∃ V : Set B, IsOpen V ∧ b ∈ V ∧ π ⁻¹' V ⊆ U := by
  refine ⟨(π '' Uᶜ)ᶜ, (hπ.isClosedMap Uᶜ hU.isClosed_compl).isOpen_compl, ?_, ?_⟩
  · rintro ⟨x,hx,hxb⟩
    exact hx (hfiber (by simpa using hxb))
  · intro x hx
    by_contra hxU
    exact hx ⟨x,hxU,rfl⟩

/-- The density step needs openness of the family map, not an analytic identity theorem. -/
theorem dense_noncentral_fibers {X B : Type*} [TopologicalSpace X]
    [TopologicalSpace B] (π : X → B) (hπ : IsOpenMap π)
    (b : B) (hdense : Dense ({b}ᶜ : Set B)) : Dense (π ⁻¹' {b}ᶜ) :=
  hdense.preimage hπ

/-- Equality of continuous sections (as maps into a Hausdorff total space)
on all noncentral fibres implies equality everywhere. -/
theorem equality_from_noncentral_fibers {X B E : Type*}
    [TopologicalSpace X] [TopologicalSpace B] [TopologicalSpace E] [T2Space E]
    (π : X → B) (hπ : IsOpenMap π) (b : B)
    (hdense : Dense ({b}ᶜ : Set B)) (s z : X → E)
    (hs : Continuous s) (hz : Continuous z)
    (haway : ∀ x, π x ≠ b → s x = z x) : s = z := by
  apply Continuous.ext_on (dense_noncentral_fibers π hπ b hdense) hs hz
  intro x hx
  exact haway x hx
end FailureOfSemipositiveMetricExtension
