import FailureOfSemipositiveMetricExtension.GeneralCanonicalNormLocalFiniteness

/-! From actual multiplier stalks to the intrinsic globally finite canonical
norm measure on the compact central manifold, in every complex dimension. -/
namespace FailureOfSemipositiveMetricExtension.GeneralCao
noncomputable section
open Set MeasureTheory Topology
open scoped Manifold ContDiff ENNReal

variable {n : ℕ} {M N : Type} [TopologicalSpace M] [ChartedSpace (Coord (n+1)) M]
    [TopologicalSpace N] [ChartedSpace (Coord n) N]
    [MeasurableSpace N] [BorelSpace N] [CompactSpace N]
    [IsManifold 𝓘(ℂ,Coord n) ω N]
    {A B J : Type} (G : Family n M N A B) (L : AnalyticLine n (M := M) J)
    (s : CentralAdjointSection n G L) (h : SemipositiveWeight n G L)

structure CanonicalNormFiniteCover where
  size : ℕ
  patch : Fin size → CanonicalNormPatch G L s h
  covers : ⋃ i, (patch i).openSet = univ

theorem canonicalNormFiniteCover_nonempty (hm : InRestrictedMultiplier n G L h s) :
    Nonempty (CanonicalNormFiniteCover G L s h) := by
  classical
  have hcover : (univ : Set N) ⊆ ⋃ P : CanonicalNormPatch G L s h, P.openSet := by
    intro p _
    exact mem_iUnion.mpr (canonicalNormPatch_at G L s h hm p)
  obtain ⟨S,hS⟩ := isCompact_univ.elim_finite_subcover CanonicalNormPatch.openSet
    CanonicalNormPatch.isOpen hcover
  let e := Fintype.equivFin S
  let P : Fin (Fintype.card S) → CanonicalNormPatch G L s h := fun i => (e.symm i).1
  refine ⟨⟨Fintype.card S,P,?_⟩⟩
  apply eq_univ_of_forall
  intro p
  have hp := hS (mem_univ p)
  simp only [mem_iUnion,exists_prop] at hp
  obtain ⟨Q,hQ,hpQ⟩ := hp
  refine mem_iUnion.mpr ⟨e ⟨Q,hQ⟩,?_⟩
  simpa only [P,Equiv.symm_apply_apply] using hpQ

namespace CanonicalNormFiniteCover
variable {G L s h} (C : CanonicalNormFiniteCover G L s h)

def measure : Measure N :=
  MeasureGluing.finiteGlue (fun i => (C.patch i).openSet) (fun i => (C.patch i).patchMeasure)

instance measure_finite : IsFiniteMeasure C.measure := by unfold measure; infer_instance

theorem measure_restrict (P : CanonicalNormPatch G L s h) :
    C.measure.restrict P.openSet = P.patchMeasure.restrict P.openSet :=
  MeasureGluing.finiteGlue_restrict_other _ _ (fun i => (C.patch i).isOpen.measurableSet)
    C.covers _ P.isOpen.measurableSet _ (fun i => (C.patch i).restrict_measures_agree P)

theorem measure_local_density (P : CanonicalNormPatch G L s h) (S : Set N)
    (hS : MeasurableSet S) (hsub : S ⊆ P.openSet) :
    C.measure S = ∫⁻ q in P.chart.chart '' S,
      s.density G L h P.chart P.frame (P.chart.chart.symm q) := by
  have he := congrArg (fun μ : Measure N => μ S) (C.measure_restrict P)
  change C.measure.restrict P.openSet S = P.patchMeasure.restrict P.openSet S at he
  rw [Measure.restrict_apply hS,Measure.restrict_apply hS,inter_eq_left.mpr hsub] at he
  exact he.trans (P.patchMeasure_apply S hS hsub)

theorem measure_unique (μ : Measure N)
    (hμ : ∀ P : CanonicalNormPatch G L s h, μ.restrict P.openSet = P.patchMeasure.restrict P.openSet) :
    μ = C.measure := by
  apply Measure.ext_of_iUnion_eq_univ C.covers
  intro i
  rw [hμ,C.measure_restrict]

theorem measure_independent (D : CanonicalNormFiniteCover G L s h) : C.measure = D.measure :=
  D.measure_unique _ C.measure_restrict

end CanonicalNormFiniteCover

/-- This is a finite intrinsic measure, uniquely determined by the true
canonical density in every valid finite coordinate ball, not an overlap sum. -/
theorem multiplier_germs_finite_canonical_norm (hm : InRestrictedMultiplier n G L h s) :
    ∃ μ : Measure N, μ univ < ⊤ ∧
      (∀ P : CanonicalNormPatch G L s h, ∀ S : Set N, MeasurableSet S → S ⊆ P.openSet →
        μ S = ∫⁻ q in P.chart.chart '' S, s.density G L h P.chart P.frame (P.chart.chart.symm q)) ∧
      (∀ ν : Measure N, (∀ P : CanonicalNormPatch G L s h,
        ν.restrict P.openSet = P.patchMeasure.restrict P.openSet) → ν = μ) := by
  let C := Classical.choice (canonicalNormFiniteCover_nonempty G L s h hm)
  exact ⟨C.measure,measure_lt_top _ _,C.measure_local_density,C.measure_unique⟩

end
end FailureOfSemipositiveMetricExtension.GeneralCao
