import FailureOfSemipositiveMetricExtension.MetricNonextension

/-! Compactness upgrades genuinely local singularity comparisons to the exact
single-constant comparison in the nonextension theorem. -/
namespace FailureOfSemipositiveMetricExtension.GlobalLineBundle
noncomputable section
open Set TopologicalSpace
open GlobalIncidence

/-- A locally uniform lower comparison, in compatible actual line frames. -/
def SingularWeightOn.centralLocallyDominatesH0 {U : Opens Total}
    (h : SingularWeightOn U (-2) (fun _ => 1)) : Prop :=
  ∀ p : Fiber 0, ∃ V : Opens (Fiber 0), p ∈ V ∧ ∃ C : ℝ,
    ∀ i q, q ∈ V → q ∈ FixedFiberBundle.baseSet 0 i →
      FixedFiberBundle.centralH0.weight i q + ((-C : ℝ) : WithBot ℝ) ≤
        h.weight i (FixedFiber.inclusion 0 q)

/-- The same singularity type means locally two-sided bounded differences,
written without undefined subtraction at a common pole. -/
def SingularWeightOn.centralLocallySameSingularityType {U : Opens Total}
    (h : SingularWeightOn U (-2) (fun _ => 1)) : Prop :=
  ∀ p : Fiber 0, ∃ V : Opens (Fiber 0), p ∈ V ∧ ∃ C : ℝ,
    ∀ i q, q ∈ V → q ∈ FixedFiberBundle.baseSet 0 i →
      FixedFiberBundle.centralH0.weight i q + ((-C : ℝ) : WithBot ℝ) ≤
        h.weight i (FixedFiber.inclusion 0 q) ∧
      h.weight i (FixedFiber.inclusion 0 q) + ((-C : ℝ) : WithBot ℝ) ≤
        FixedFiberBundle.centralH0.weight i q

theorem SingularWeightOn.centralLocallyDominatesH0_dominates {U : Opens Total}
    (h : SingularWeightOn U (-2) (fun _ => 1)) (hc : h.centralLocallyDominatesH0) :
    h.centralDominatesH0 := by
  classical
  choose V hpV C hC using hc
  have hcover : (Set.univ : Set (Fiber 0)) ⊆ ⋃ p, (V p : Set (Fiber 0)) := by
    intro p _
    exact mem_iUnion.mpr ⟨p,hpV p⟩
  obtain ⟨S,hS⟩ := isCompact_univ.elim_finite_subcover (fun p => (V p : Set (Fiber 0)))
    (fun p => (V p).isOpen) hcover
  let B : ℝ := ∑ p ∈ S, |C p|
  refine ⟨B,?_⟩
  intro i q hq
  obtain ⟨p,hp,hqp⟩ := (show ∃ p ∈ S, q ∈ V p by
    simpa only [mem_iUnion,exists_prop] using hS (mem_univ q))
  have hCB : C p ≤ B := (le_abs_self _).trans
    (Finset.single_le_sum (fun p _ => abs_nonneg (C p)) hp)
  exact (add_le_add_left (WithBot.coe_le_coe.mpr (neg_le_neg hCB)) _).trans
    (hC p i q hqp hq)

/-- A lower comparison verified in any chosen local frame transfers to every
other compatible frame; no sign choice for the transition is suppressed. -/
theorem SingularWeightOn.centralComparison_frame_transfer {U : Opens Total}
    (h : SingularWeightOn U (-2) (fun _ => 1)) (hU : ContainsCentralFiber U)
    (i j : Index) (p : Fiber 0) (hi : p ∈ FixedFiberBundle.baseSet 0 i)
    (hj : p ∈ FixedFiberBundle.baseSet 0 j) (C : ℝ)
    (hc : FixedFiberBundle.centralH0.weight i p + ((-C : ℝ) : WithBot ℝ) ≤
      h.weight i (FixedFiber.inclusion 0 p)) :
    FixedFiberBundle.centralH0.weight j p + ((-C : ℝ) : WithBot ℝ) ≤
      h.weight j (FixedFiber.inclusion 0 p) := by
  rw [FixedFiberBundle.centralH0.compatible i j p ⟨hi,hj⟩,
    h.compatible i j _ (hU p) ⟨hi,hj⟩,add_right_comm]
  exact add_le_add_right hc _

/-- Thus the local comparison may be given in just one genuine trivialization
around each point, exactly as in the usual definition of singularity type. -/
theorem SingularWeightOn.centralLocallyDominatesH0_of_local_frames {U : Opens Total}
    (h : SingularWeightOn U (-2) (fun _ => 1)) (hU : ContainsCentralFiber U)
    (hc : ∀ p : Fiber 0, ∃ (i : Index) (V : Opens (Fiber 0)), p ∈ V ∧
      (V : Set (Fiber 0)) ⊆ FixedFiberBundle.baseSet 0 i ∧ ∃ C : ℝ,
      ∀ q ∈ V, FixedFiberBundle.centralH0.weight i q + ((-C : ℝ) : WithBot ℝ) ≤
        h.weight i (FixedFiber.inclusion 0 q)) : h.centralLocallyDominatesH0 := by
  intro p
  obtain ⟨i,V,hp,hV,C,hC⟩ := hc p
  exact ⟨V,hp,C,fun j q hq hj => h.centralComparison_frame_transfer hU i j q
    (hV hq) hj C (hC q hq)⟩

theorem no_semipositive_extension_same_local_singularity_type (U : Opens Total)
    (hU : ContainsCentralFiber U) :
    ¬ ∃ h : SingularWeightOn U (-2) (fun _ => 1),
      h.HasPlurisubharmonicWeights ∧ h.centralLocallySameSingularityType := by
  rintro ⟨h,hpsh,hc⟩
  apply no_semipositive_metric_dominating_centralH0 U hU
  refine ⟨h,hpsh,h.centralLocallyDominatesH0_dominates ?_⟩
  intro p
  obtain ⟨V,hp,C,hC⟩ := hc p
  exact ⟨V,hp,C,fun i q hq hi => (hC i q hq hi).1⟩

end
end FailureOfSemipositiveMetricExtension.GlobalLineBundle
