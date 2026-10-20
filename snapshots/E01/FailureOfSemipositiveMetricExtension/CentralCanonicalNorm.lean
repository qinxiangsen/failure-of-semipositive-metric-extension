import FailureOfSemipositiveMetricExtension.CentralPatchMeasureAgreement
import FailureOfSemipositiveMetricExtension.FiniteMeasureGluing

/-! The intrinsic canonical L2 norm measure of the actual sigma and h0^4.
It is characterized by its actual Lebesgue densities on ALL coordinate balls,
independent of the chosen finite cover. It has finite total mass. The convention
uses standard real Lebesgue area in each complex coordinate. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set MeasureTheory Topology
open scoped ENNReal
attribute [local instance] centralBorel centralBorelSpace

structure CentralNormFiniteCover where
  size : ℕ
  patch : Fin size → CentralNormPatch
  covers : ⋃ i, (patch i).openSet = univ

theorem centralNormFiniteCover_nonempty : Nonempty CentralNormFiniteCover := by
  classical
  obtain ⟨S,hS⟩ := exists_finite_centralNormPatch_cover
  let e := Fintype.equivFin S
  let P : Fin (Fintype.card S) → CentralNormPatch := fun i => (e.symm i).1
  refine ⟨⟨Fintype.card S,P,?_⟩⟩
  apply eq_univ_of_forall
  intro p
  obtain ⟨Q,hQ,hp⟩ := hS p
  refine mem_iUnion.mpr ⟨e ⟨Q,hQ⟩,?_⟩
  simpa only [P,Equiv.symm_apply_apply] using hp

def CentralNormFiniteCover.measure (C : CentralNormFiniteCover) : Measure (Fiber 0) :=
  MeasureGluing.finiteGlue (fun i => (C.patch i).openSet) (fun i => (C.patch i).pushforwardMeasure)

instance CentralNormFiniteCover.measure_finite (C : CentralNormFiniteCover) :
    IsFiniteMeasure C.measure := by
  unfold CentralNormFiniteCover.measure
  infer_instance

/-- Every chart, including charts not in the chosen finite cover, recovers the
same local norm measure. -/
theorem CentralNormFiniteCover.measure_restrict (C : CentralNormFiniteCover) (P : CentralNormPatch) :
    C.measure.restrict P.openSet = P.pushforwardMeasure.restrict P.openSet :=
  MeasureGluing.finiteGlue_restrict_other _ _ (fun i => (C.patch i).isOpen.measurableSet)
    C.covers _ P.isOpen.measurableSet _ (fun i => (C.patch i).restrict_measures_agree P)

theorem CentralNormFiniteCover.measure_independent (C D : CentralNormFiniteCover) :
    C.measure = D.measure := by
  apply Measure.ext_of_iUnion_eq_univ C.covers
  intro i
  rw [C.measure_restrict,D.measure_restrict]

def centralNormChosenCover : CentralNormFiniteCover := Classical.choice centralNormFiniteCover_nonempty

def centralCanonicalNormMeasure : Measure (Fiber 0) := centralNormChosenCover.measure

instance centralCanonicalNormMeasure_finite : IsFiniteMeasure centralCanonicalNormMeasure :=
  CentralNormFiniteCover.measure_finite _

theorem centralCanonicalNormMeasure_restrict (P : CentralNormPatch) :
    centralCanonicalNormMeasure.restrict P.openSet = P.pushforwardMeasure.restrict P.openSet :=
  centralNormChosenCover.measure_restrict P

/-- The intrinsic measure has exactly the actual canonical coefficient density
in every valid coordinate ball, not an overlap-multiplicity sum. -/
theorem centralCanonicalNormMeasure_local_density (P : CentralNormPatch) (S : Set (Fiber 0))
    (hS : MeasurableSet S) (hsub : S ⊆ P.openSet) :
    centralCanonicalNormMeasure S = ∫⁻ q in FixedFiber.coordinates 0 P.frame.1 P.frame.2.1 '' S,
      sigmaAdjointExtendedDensity P.frame (FixedFiber.param 0 P.frame.1 P.frame.2.1 q) := by
  have h := congrArg (fun μ : Measure (Fiber 0) => μ S) (centralCanonicalNormMeasure_restrict P)
  change centralCanonicalNormMeasure.restrict P.openSet S = P.pushforwardMeasure.restrict P.openSet S at h
  rw [Measure.restrict_apply hS,Measure.restrict_apply hS,inter_eq_left.mpr hsub] at h
  exact h.trans (P.pushforwardMeasure_apply S hS hsub)

theorem centralCanonicalNormMeasure_unique (ν : Measure (Fiber 0))
    (hν : ∀ P : CentralNormPatch, ν.restrict P.openSet = P.pushforwardMeasure.restrict P.openSet) :
    ν = centralCanonicalNormMeasure := by
  apply Measure.ext_of_iUnion_eq_univ centralNormChosenCover.covers
  intro i
  rw [hν,centralCanonicalNormMeasure_restrict]

def sigmaGlobalNormSquared : ℝ≥0∞ := centralCanonicalNormMeasure univ

/-- The actual canonical-times-L4 section has finite intrinsic global weighted
L2 norm on the whole compact central surface. -/
theorem sigma_global_norm_finite : sigmaGlobalNormSquared < ⊤ :=
  measure_lt_top _ _

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
