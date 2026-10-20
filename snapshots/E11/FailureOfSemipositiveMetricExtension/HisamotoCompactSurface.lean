import FailureOfSemipositiveMetricExtension.HisamotoStrictTransform
import FailureOfSemipositiveMetricExtension.ProjectiveIncidence

/-! Compactness and properness for the actual one-point projective incidence
surface. Only one direction is present; no identification with the independent
four-centre family is made. -/
namespace FailureOfSemipositiveMetricExtension.Hisamoto
noncomputable section
open Set Topology

abbrev Ambient := PlanePoint × Direction

def ambientChart (a : Fin 3) : Set Ambient := {q | q.1 ∈ ProjectivePlane.chartSet a}
def normalizedPair (a : Fin 3) (q : Ambient) : Fin 2 → ℂ :=
  centrePair (ProjectivePlane.vector a (ProjectivePlane.coordinates a q.1))

theorem ambientChart_isOpen (a : Fin 3) : IsOpen (ambientChart a) :=
  (ProjectivePlane.chartSet_isOpen a).preimage continuous_fst

theorem ambientChart_cover : (⋃ a, ambientChart a) = univ := by
  ext q
  simp only [mem_iUnion,mem_univ,iff_true]
  obtain ⟨a,u,hu⟩ := ProjectivePlane.charts_cover q.1
  exact ⟨a,u,hu.symm⟩

theorem normalizedPair_continuousOn (a : Fin 3) : ContinuousOn (normalizedPair a) (ambientChart a) := by
  have hc : ContinuousOn (fun q : Ambient => ProjectivePlane.coordinates a q.1) (ambientChart a) :=
    (ProjectivePlane.homeomorphChart a).continuousOn.comp continuous_fst.continuousOn (fun _ h => h)
  exact (centrePair_contDiff 0).continuous.comp_continuousOn
    ((planeVector_contDiff a 0).continuous.comp_continuousOn hc)

theorem incidence_normalizedPair_iff (a : Fin 3) (q : Ambient) (hq : q ∈ ambientChart a) :
    Incidence q.1 q.2 ↔ normalizedPair a q ∈ q.2.submodule := by
  conv_lhs => rw [← ProjectivePlane.param_coordinates a q.1 hq]
  exact incidence_mk_iff _ _ _

theorem incidenceLocus_isClosed : IsClosed {q : Ambient | Incidence q.1 q.2} := by
  rw [← isOpen_compl_iff]
  apply (isOpen_iff_of_cover ambientChart_isOpen ambientChart_cover).mpr
  intro a
  let f : Ambient → (Fin 2 → ℂ) × Direction := fun q => (normalizedPair a q,q.2)
  have hf : ContinuousOn f (ambientChart a) := (normalizedPair_continuousOn a).prodMk continuous_snd.continuousOn
  have he : ambientChart a ∩ {q : Ambient | Incidence q.1 q.2}ᶜ =
      ambientChart a ∩ f ⁻¹' {p : (Fin 2 → ℂ) × Direction | p.1 ∈ p.2.submodule}ᶜ := by
    ext q
    simp only [mem_inter_iff,mem_compl_iff,mem_preimage,mem_setOf_eq]
    exact and_congr_right (fun hq => not_congr (incidence_normalizedPair_iff a q hq))
  rw [he]
  exact hf.isOpen_inter_preimage (ambientChart_isOpen a) ProjectiveIncidence.isClosed_incidence.isOpen_compl

instance instCompactSpacePoint : CompactSpace Point :=
  isCompact_iff_compactSpace.mp incidenceLocus_isClosed.isCompact

/-- The true incidence inclusion is a closed embedding into P²×P¹. -/
theorem incidence_inclusion_isClosedEmbedding : Topology.IsClosedEmbedding (Subtype.val : Point → Ambient) :=
  incidenceLocus_isClosed.isClosedEmbedding_subtypeVal

theorem blowdown_isProperMap : IsProperMap blowdown := blowdown_continuous.isProperMap
theorem ruling_isProperMap : IsProperMap ruling := ruling_continuous.isProperMap

end
end FailureOfSemipositiveMetricExtension.Hisamoto
