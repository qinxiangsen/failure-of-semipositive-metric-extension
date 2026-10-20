import FailureOfSemipositiveMetricExtension.GlobalIncidence
import FailureOfSemipositiveMetricExtension.ProjectiveIncidence
import FailureOfSemipositiveMetricExtension.ProjectivePlaneFamily

/-! The global four-centre incidence space as a closed subspace of the genuine
projective ambient product. Its parameter projection is proper. No global
continuous representative and no smoothness assumption are used. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence
noncomputable section
open Set

abbrev Ambient := PlanePoint × (Fin 4 → Direction) × ℂ

def ambientChart (a : Fin 3) : Set Ambient :=
  {q | q.1 ∈ FailureOfSemipositiveMetricExtension.ProjectivePlane.chartSet a}

def localPair (a : Fin 3) (i : Fin 4) (q : Ambient) : Fin 2 → ℂ :=
  pairMap i q.2.2 (FailureOfSemipositiveMetricExtension.ProjectivePlane.vector a
    (FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates a q.1))

theorem ambientChart_isOpen (a : Fin 3) : IsOpen (ambientChart a) :=
  (FailureOfSemipositiveMetricExtension.ProjectivePlane.chartSet_isOpen a).preimage continuous_fst

theorem ambientChart_cover : (⋃ a, ambientChart a) = univ := by
  ext q
  simp only [mem_iUnion,mem_univ,iff_true]
  obtain ⟨a,u,hu⟩ := FailureOfSemipositiveMetricExtension.ProjectivePlane.charts_cover q.1
  exact ⟨a,u,hu.symm⟩

theorem normalizedVector_continuous (a : Fin 3) :
    Continuous (FailureOfSemipositiveMetricExtension.ProjectivePlane.vector a) := by
  apply continuous_pi
  intro j
  fin_cases a <;> fin_cases j <;> dsimp [FailureOfSemipositiveMetricExtension.ProjectivePlane.vector]
  all_goals first | exact continuous_const | exact continuous_fst | exact continuous_snd

theorem pairMap_continuous (i : Fin 4) :
    Continuous (fun q : ℂ × (Fin 3 → ℂ) => pairMap i q.1 q.2) := by
  have h0 : Continuous (fun q : ℂ × (Fin 3 → ℂ) => q.2 0) :=
    (continuous_apply 0).comp continuous_snd
  have h1 : Continuous (fun q : ℂ × (Fin 3 → ℂ) => q.2 1) :=
    (continuous_apply 1).comp continuous_snd
  have h2 : Continuous (fun q : ℂ × (Fin 3 → ℂ) => q.2 2) :=
    (continuous_apply 2).comp continuous_snd
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> dsimp [pairMap,pair]
  · exact h1
  · exact h2
  · exact h0
  · exact h2
  · exact h1.sub h0
  · exact h2.sub (continuous_fst.mul h0)
  · exact h0
  · exact h1

theorem ambientCoordinates_continuousOn (a : Fin 3) :
    ContinuousOn (fun q : Ambient => FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates a q.1)
      (ambientChart a) := by
  have hc : ContinuousOn (FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates a)
      (FailureOfSemipositiveMetricExtension.ProjectivePlane.chartSet a) :=
    (FailureOfSemipositiveMetricExtension.ProjectivePlane.homeomorphChart a).continuousOn
  exact hc.comp continuous_fst.continuousOn (fun _ h => h)

theorem localPair_continuousOn (a : Fin 3) (i : Fin 4) :
    ContinuousOn (localPair a i) (ambientChart a) := by
  have hv (j : Fin 3) : ContinuousOn (fun q : Ambient =>
      FailureOfSemipositiveMetricExtension.ProjectivePlane.vector a
        (FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates a q.1) j) (ambientChart a) :=
    (FailureOfSemipositiveMetricExtension.ProjectivePlane.vector_component_continuous a j).comp_continuousOn
      (ambientCoordinates_continuousOn a)
  have ht : ContinuousOn (fun q : Ambient => q.2.2) (ambientChart a) :=
    (continuous_snd.comp continuous_snd).continuousOn
  rw [continuousOn_pi]
  intro j
  fin_cases i <;> fin_cases j
  · exact hv 1
  · exact hv 2
  · exact hv 0
  · exact hv 2
  · exact (hv 1).sub (hv 0)
  · exact (hv 2).sub (ht.mul (hv 0))
  · exact hv 0
  · exact hv 1

theorem incidence_localPair_iff (a : Fin 3) (i : Fin 4) (q : Ambient)
    (hq : q ∈ ambientChart a) :
    Incidence q.1 (q.2.1 i) i q.2.2 ↔ localPair a i q ∈ (q.2.1 i).submodule := by
  conv_lhs => rw [← FailureOfSemipositiveMetricExtension.ProjectivePlane.param_coordinates a q.1 hq]
  exact incidence_mk_iff _ _ _ _ _

def incidenceLocus (i : Fin 4) : Set Ambient := {q | Incidence q.1 (q.2.1 i) i q.2.2}

theorem incidenceLocus_isClosed (i : Fin 4) : IsClosed (incidenceLocus i) := by
  rw [← isOpen_compl_iff]
  apply (isOpen_iff_of_cover ambientChart_isOpen ambientChart_cover).mpr
  intro a
  let f : Ambient → (Fin 2 → ℂ) × Direction := fun q => (localPair a i q,q.2.1 i)
  have hf : ContinuousOn f (ambientChart a) := (localPair_continuousOn a i).prodMk (by fun_prop)
  have heq : ambientChart a ∩ (incidenceLocus i)ᶜ =
      ambientChart a ∩ f ⁻¹' {p : (Fin 2 → ℂ) × Direction | p.1 ∈ p.2.submodule}ᶜ := by
    ext q
    simp only [mem_inter_iff,mem_compl_iff,mem_preimage,mem_setOf_eq,incidenceLocus]
    exact and_congr_right (fun hq => not_congr (incidence_localPair_iff a i q hq))
  rw [heq]
  exact hf.isOpen_inter_preimage (ambientChart_isOpen a)
    FailureOfSemipositiveMetricExtension.ProjectiveIncidence.isClosed_incidence.isOpen_compl

def totalLocus : Set Ambient := {q | ∀ i, Incidence q.1 (q.2.1 i) i q.2.2}

theorem totalLocus_isClosed : IsClosed totalLocus := by
  have heq : totalLocus = ⋂ i, incidenceLocus i := by ext q; simp [totalLocus,incidenceLocus]
  rw [heq]
  exact isClosed_iInter incidenceLocus_isClosed

/-- The global incidence space carries precisely the ambient subspace topology. -/
instance instTopologicalSpaceTotal : TopologicalSpace Total :=
  inferInstanceAs (TopologicalSpace {q : Ambient // q ∈ totalLocus})

instance instT2SpaceTotal : T2Space Total :=
  inferInstanceAs (T2Space {q : Ambient // q ∈ totalLocus})

instance instSecondCountableTopologyTotal : SecondCountableTopology Total :=
  inferInstanceAs (SecondCountableTopology {q : Ambient // q ∈ totalLocus})

theorem total_inclusion_isClosedEmbedding :
    Topology.IsClosedEmbedding (Subtype.val : Total → Ambient) :=
  totalLocus_isClosed.isClosedEmbedding_subtypeVal

def ambientProjection (q : Ambient) : ℂ := q.2.2

theorem ambientProjection_isProperMap : IsProperMap ambientProjection := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨continuous_snd.comp continuous_snd,fun K hK => ?_⟩
  have heq : ambientProjection ⁻¹' K =
      (univ : Set PlanePoint) ×ˢ ((univ : Set (Fin 4 → Direction)) ×ˢ K) := by
    ext q; simp [ambientProjection]
  rw [heq]
  exact isCompact_univ.prod (isCompact_univ.prod hK)

/-- The actual global four-centre incidence family is proper over the parameter line. -/
theorem projection_isProperMap : IsProperMap projection :=
  total_inclusion_isClosedEmbedding.isProperMap.comp ambientProjection_isProperMap

theorem projection_continuous : Continuous projection := projection_isProperMap.continuous

theorem global_fiber_neighborhood (t : ℂ) (U : Set Total) (hU : IsOpen U)
    (hfiber : projection ⁻¹' {t} ⊆ U) :
    ∃ V : Set ℂ, IsOpen V ∧ t ∈ V ∧ projection ⁻¹' V ⊆ U :=
  FailureOfSemipositiveMetricExtension.proper_fiber_neighborhood projection projection_isProperMap t U hU hfiber

/-- The independently defined fibre is a closed subset of P²×(P¹)^4. -/
theorem fiberLocus_isClosed (t : ℂ) :
    IsClosed {q : PlanePoint × (Fin 4 → Direction) | ∀ i, Incidence q.1 (q.2 i) i t} := by
  exact totalLocus_isClosed.preimage (show Continuous (fun q : PlanePoint × (Fin 4 → Direction) =>
    (q.1,q.2,t)) by fun_prop)

instance instTopologicalSpaceFiber (t : ℂ) : TopologicalSpace (Fiber t) :=
  inferInstanceAs (TopologicalSpace {q : PlanePoint × (Fin 4 → Direction) |
    ∀ i, Incidence q.1 (q.2 i) i t})

instance instCompactSpaceFiber (t : ℂ) : CompactSpace (Fiber t) :=
  isCompact_iff_compactSpace.mp (fiberLocus_isClosed t).isCompact

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence
