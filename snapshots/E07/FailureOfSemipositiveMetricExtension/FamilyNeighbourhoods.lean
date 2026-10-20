import FailureOfSemipositiveMetricExtension.GlobalSubmersion
import FailureOfSemipositiveMetricExtension.GlobalFiberManifold

/-! Shrinking any actual neighbourhood of the whole central fibre to a full
parameter disc, and density of noncentral fibres in the original topology. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence
noncomputable section
open Set Topology TopologicalSpace

/-- Every actual point of the level set is represented by the independently
constructed fibre, with equality in the original total space. -/
theorem exists_fiber_inclusion (t : ℂ) (p : Total) (hp : projection p = t) :
    ∃ q : Fiber t, FixedFiber.inclusion t q = p := by
  subst t
  exact ⟨⟨(blowdown p,directions p),p.property⟩,rfl⟩

theorem range_fiber_inclusion (t : ℂ) :
    range (FixedFiber.inclusion t) = projection ⁻¹' {t} := by
  ext p
  constructor
  · rintro ⟨q,rfl⟩
    rfl
  · intro hp
    exact exists_fiber_inclusion t p hp

/-- Properness gives an actual open neighbourhood in the base whose entire
inverse image is contained in the specified total-space neighbourhood. -/
theorem contains_full_fibres_near_zero (U : Opens Total)
    (hU : ∀ p : Fiber 0, FixedFiber.inclusion 0 p ∈ U) :
    ∃ V : Opens ℂ, 0 ∈ V ∧ projection ⁻¹' (V : Set ℂ) ⊆ U := by
  let V : Opens ℂ := ⟨(projection '' (U : Set Total)ᶜ)ᶜ,
    (projection_isProperMap.isClosedMap _ U.isOpen.isClosed_compl).isOpen_compl⟩
  refine ⟨V,?_,?_⟩
  · rintro ⟨p,hp,hp0⟩
    obtain ⟨q,rfl⟩ := exists_fiber_inclusion 0 p hp0
    exact hp (hU q)
  · intro p hp
    by_contra hn
    exact hp ⟨p,hn,rfl⟩

/-- The quantifier is a strictly positive radius, not a pointwise or punctured
neighbourhood: every fibre over that disc is inside U. -/
theorem contains_full_disc_near_zero (U : Opens Total)
    (hU : ∀ p : Fiber 0, FixedFiber.inclusion 0 p ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ projection ⁻¹' Metric.ball (0 : ℂ) ε ⊆ U := by
  obtain ⟨V,hV,hVU⟩ := contains_full_fibres_near_zero U hU
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp V.isOpen 0 hV
  exact ⟨ε,hε,fun _ hp => hVU (hball hp)⟩

/-- Noncentral fibres are actually dense; this follows from the proved openness
of the actual family projection, without any assumed irreducibility. -/
theorem noncentral_fibres_dense : Dense {p : Total | projection p ≠ 0} :=
  (dense_compl_singleton (0 : ℂ)).preimage projection_isOpenMap

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence
