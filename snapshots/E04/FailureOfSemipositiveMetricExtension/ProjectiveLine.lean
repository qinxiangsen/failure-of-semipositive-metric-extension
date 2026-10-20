import FailureOfSemipositiveMetricExtension.BlowupAtlas
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
The actual projectivization of the complex two-dimensional vector space, with its two
standard affine charts. The topology, analytic manifold, Hausdorffness, second
countability, and compactness are all constructed from those charts.
-/

noncomputable section

namespace FailureOfSemipositiveMetricExtension.ProjectiveLine

open Set Topology
open scoped Manifold ContDiff

/-- The actual quotient of nonzero homogeneous vectors by complex scalar equivalence. -/
abbrev Point := Projectivization ℂ (Fin 2 → ℂ)

/-- The two standard affine parametrizations `[1:s]` and `[s:1]`. -/
def param (i : Fin 2) (s : ℂ) : Point :=
  if i = 0 then Blowup.lineX s else Blowup.lineY s

@[simp] theorem param_zero (s : ℂ) : param 0 s = Blowup.lineX s := by simp [param]
@[simp] theorem param_one (s : ℂ) : param 1 s = Blowup.lineY s := by simp [param]

theorem param_injective (i : Fin 2) : Function.Injective (param i) := by
  fin_cases i
  · exact Blowup.lineX_injective
  · exact Blowup.lineY_injective

/-- The source of each projective affine chart. -/
def chartSet (i : Fin 2) : Set Point := range (param i)

/-- The two standard affine normalizations cover every projective point. -/
theorem charts_cover (p : Point) : ∃ i s, p = param i s := by
  rcases Blowup.direction_cover p with ⟨s,hs⟩ | ⟨s,hs⟩
  · exact ⟨0,s,hs⟩
  · exact ⟨1,s,hs⟩

/-- The full affine domain on the diagonal and the punctured affine line otherwise. -/
def overlap (i j : Fin 2) : Set ℂ := if i = j then univ else {s | s ≠ 0}

/-- The projective transition map is inversion between different affine charts. -/
def transition (i j : Fin 2) (s : ℂ) : ℂ := if i = j then s else s⁻¹

theorem lineX_mem_range_lineY_iff (s : ℂ) :
    Blowup.lineX s ∈ range Blowup.lineY ↔ s ≠ 0 := by
  constructor
  · rintro ⟨t,ht⟩ hs
    have he := (Blowup.lineX_eq_lineY_iff s t).mp ht.symm
    simp [hs] at he
  · intro hs
    exact ⟨s⁻¹,(Blowup.lineX_eq_lineY_inv s hs).symm⟩

theorem lineY_mem_range_lineX_iff (s : ℂ) :
    Blowup.lineY s ∈ range Blowup.lineX ↔ s ≠ 0 := by
  constructor
  · rintro ⟨t,ht⟩ hs
    have he := (Blowup.lineX_eq_lineY_iff t s).mp ht
    simp [hs] at he
  · intro hs
    exact ⟨s⁻¹,by simpa using Blowup.lineX_eq_lineY_inv s⁻¹ (inv_ne_zero hs)⟩

@[simp] theorem param_mem_chartSet_iff (i j : Fin 2) (s : ℂ) :
    param i s ∈ chartSet j ↔ s ∈ overlap i j := by
  fin_cases i <;> fin_cases j
  · simp [chartSet,overlap]
  · simpa [chartSet,overlap,param] using lineX_mem_range_lineY_iff s
  · simpa [chartSet,overlap,param] using lineY_mem_range_lineX_iff s
  · simp [chartSet,overlap]

theorem param_transition (i j : Fin 2) (s : ℂ) (hs : s ∈ overlap i j) :
    param i s = param j (transition i j s) := by
  fin_cases i <;> fin_cases j
  · rfl
  · exact Blowup.lineX_eq_lineY_inv s hs
  · simpa [param,transition] using (Blowup.lineX_eq_lineY_inv s⁻¹ (inv_ne_zero hs)).symm
  · rfl

/-- Coordinates extended arbitrarily outside the affine chart. -/
def coordinates (i : Fin 2) : Point → ℂ := Function.invFun (param i)

@[simp] theorem coordinates_param (i : Fin 2) (s : ℂ) :
    coordinates i (param i s) = s := Function.leftInverse_invFun (param_injective i) s

theorem param_coordinates (i : Fin 2) (p : Point) (hp : p ∈ chartSet i) :
    param i (coordinates i p) = p := by
  rcases hp with ⟨s,rfl⟩
  rw [coordinates_param]

/-- Each affine chart is a genuine partial equivalence with target all of `ℂ`. -/
def partialChart (i : Fin 2) : PartialEquiv Point ℂ where
  toFun := coordinates i
  invFun := param i
  source := chartSet i
  target := univ
  map_source' _ _ := mem_univ _
  map_target' s _ := ⟨s,rfl⟩
  left_inv' := param_coordinates i
  right_inv' s _ := coordinates_param i s

@[simp] theorem partialChart_source (i : Fin 2) : (partialChart i).source = chartSet i := rfl
@[simp] theorem partialChart_target (i : Fin 2) : (partialChart i).target = univ := rfl
@[simp] theorem partialChart_symm_apply (i : Fin 2) (s : ℂ) :
    (partialChart i).symm s = param i s := rfl

theorem coordinates_transition (i j : Fin 2) (s : ℂ) (hs : s ∈ overlap i j) :
    coordinates j (param i s) = transition i j s := by
  rw [param_transition i j s hs,coordinates_param]

@[simp] theorem partialChart_transition_source (i j : Fin 2) :
    ((partialChart i).symm.trans (partialChart j)).source = overlap i j := by
  ext s
  simpa [PartialEquiv.trans_source] using param_mem_chartSet_iff i j s

theorem partialChart_transition_apply (i j : Fin 2) (s : ℂ)
    (hs : s ∈ overlap i j) :
    ((partialChart i).symm.trans (partialChart j)) s = transition i j s :=
  coordinates_transition i j s hs

theorem overlap_isOpen (i j : Fin 2) : IsOpen (overlap i j) := by
  by_cases h : i = j
  · simp [overlap,h]
  · simpa [overlap,h] using (isOpen_ne : IsOpen {s : ℂ | s ≠ 0})

/-- All transition maps are complex analytic on the actual overlap. -/
theorem transition_contDiffOn (i j : Fin 2) (n : WithTop ℕ∞) :
    ContDiffOn ℂ n (transition i j) (overlap i j) := by
  change ContDiffOn ℂ n (fun s => if i = j then s else s⁻¹) (overlap i j)
  by_cases h : i = j
  · simpa [overlap,h] using (contDiffOn_id : ContDiffOn ℂ n (id : ℂ → ℂ) univ)
  · simp only [overlap,if_neg h]
    exact contDiffOn_id.inv (fun s (hs : s ∈ {s : ℂ | s ≠ 0}) => hs)

theorem transition_continuousOn (i j : Fin 2) :
    ContinuousOn (transition i j) (overlap i j) :=
  (transition_contDiffOn i j 0).continuousOn

/-- Explicit charted-space core, including every overlap and continuity obligation. -/
def atlasCore : ChartedSpaceCore ℂ Point where
  atlas := range partialChart
  chartAt p := partialChart (Classical.choose (charts_cover p))
  mem_chart_source p := by
    obtain ⟨s,hs⟩ := Classical.choose_spec (charts_cover p)
    exact ⟨s,hs.symm⟩
  chart_mem_atlas p := ⟨_,rfl⟩
  open_source e e' he he' := by
    rcases he with ⟨i,rfl⟩
    rcases he' with ⟨j,rfl⟩
    rw [partialChart_transition_source]
    exact overlap_isOpen i j
  continuousOn_toFun e e' he he' := by
    rcases he with ⟨i,rfl⟩
    rcases he' with ⟨j,rfl⟩
    rw [partialChart_transition_source]
    exact (transition_continuousOn i j).congr (partialChart_transition_apply i j)

/-- The standard affine-atlas topology on the actual projectivization quotient. -/
instance instTopologicalSpacePoint : TopologicalSpace Point := atlasCore.toTopologicalSpace

instance instChartedSpacePoint : ChartedSpace ℂ Point := atlasCore.toChartedSpace

/-- Each standard affine chart, with its verified continuity in both directions. -/
def homeomorphChart (i : Fin 2) : PartialHomeomorph Point ℂ :=
  atlasCore.partialHomeomorph (partialChart i) ⟨i,rfl⟩

@[simp] theorem homeomorphChart_source (i : Fin 2) :
    (homeomorphChart i).source = chartSet i := rfl
@[simp] theorem homeomorphChart_target (i : Fin 2) :
    (homeomorphChart i).target = univ := rfl
@[simp] theorem homeomorphChart_symm_apply (i : Fin 2) (s : ℂ) :
    (homeomorphChart i).symm s = param i s := rfl

theorem chartSet_isOpen (i : Fin 2) : IsOpen (chartSet i) := (homeomorphChart i).open_source

theorem param_continuous (i : Fin 2) : Continuous (param i) :=
  continuous_iff_continuousOn_univ.mpr (homeomorphChart i).continuousOn_symm

theorem param_isOpenEmbedding (i : Fin 2) : Topology.IsOpenEmbedding (param i) :=
  (homeomorphChart i).symm.to_isOpenEmbedding rfl

/-- The two-chart cover proves second countability. -/
instance instSecondCountableTopologyPoint : SecondCountableTopology Point := by
  haveI : ∀ i, SecondCountableTopology (chartSet i) :=
    fun i => (homeomorphChart i).secondCountableTopology_source
  apply TopologicalSpace.secondCountableTopology_of_countable_cover (U := chartSet)
  · exact chartSet_isOpen
  · ext p
    simp only [mem_iUnion,mem_univ,iff_true]
    obtain ⟨i,s,hs⟩ := charts_cover p
    exact ⟨i,s,hs.symm⟩

/-- The installed atlas consists exactly of the two constructed charts. -/
theorem mem_atlas_iff (e : PartialHomeomorph Point ℂ) :
    e ∈ atlas ℂ Point ↔ ∃ i, e = homeomorphChart i := by
  change (e ∈ ⋃ (f : PartialEquiv Point ℂ) (hf : f ∈ atlasCore.atlas),
    {atlasCore.partialHomeomorph f hf}) ↔ _
  simp only [mem_iUnion,mem_singleton_iff]
  constructor
  · rintro ⟨f,⟨i,rfl⟩,rfl⟩
    exact ⟨i,rfl⟩
  · rintro ⟨i,rfl⟩
    exact ⟨partialChart i,⟨i,rfl⟩,rfl⟩

theorem atlas_contDiffOn (n : WithTop ℕ∞) (e e' : PartialHomeomorph Point ℂ)
    (he : e ∈ atlas ℂ Point) (he' : e' ∈ atlas ℂ Point) :
    ContDiffOn ℂ n (e.symm.trans e') (e.symm.trans e').source := by
  rcases (mem_atlas_iff e).mp he with ⟨i,rfl⟩
  rcases (mem_atlas_iff e').mp he' with ⟨j,rfl⟩
  change ContDiffOn ℂ n ((partialChart i).symm.trans (partialChart j))
    ((partialChart i).symm.trans (partialChart j)).source
  rw [partialChart_transition_source]
  exact (transition_contDiffOn i j n).congr (partialChart_transition_apply i j)

/-- Complex-manifold compatibility at every regularity, including analytic. -/
instance instIsManifoldPoint (n : WithTop ℕ∞) : IsManifold 𝓘(ℂ) n Point := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  simpa using atlas_contDiffOn n e e' he he'

theorem complex_analytic_manifold : IsManifold 𝓘(ℂ) ω Point := inferInstance

/-- Equal points in opposite normalized charts satisfy the reciprocal relation. -/
theorem cross_ratio_eq_one (i j : Fin 2) (hij : i ≠ j) (s t : ℂ)
    (h : param i s = param j t) : s*t = 1 := by
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact (Blowup.lineX_eq_lineY_iff s t).mp h
  · simpa [mul_comm] using (Blowup.lineX_eq_lineY_iff t s).mp h.symm
  · exact (hij rfl).elim

private def Separated (p q : Point) : Prop :=
  ∃ U V : Set Point, IsOpen U ∧ IsOpen V ∧ p ∈ U ∧ q ∈ V ∧ Disjoint U V

private theorem separate_same_chart (i : Fin 2) (s t : ℂ)
    (h : param i s ≠ param i t) : Separated (param i s) (param i t) := by
  apply separated_by_isOpenEmbedding (x := s) (y := t) (param_isOpenEmbedding i)
  intro he
  exact h (congrArg (param i) he)

/-- Opposite affine unit discs have disjoint images. -/
theorem small_slope_images_disjoint (i j : Fin 2) (hij : i ≠ j) :
    Disjoint (param i '' {s | ‖s‖ < 1}) (param j '' {s | ‖s‖ < 1}) := by
  rw [Set.disjoint_left]
  rintro p ⟨s,hs,hsp⟩ ⟨t,ht,htp⟩
  have hprod := cross_ratio_eq_one i j hij s t (hsp.trans htp.symm)
  have hnorm : ‖s‖ * ‖t‖ = 1 := by rw [← norm_mul,hprod,norm_one]
  have hlt : ‖s‖ * ‖t‖ < 1 := calc
    _ ≤ 1 * ‖t‖ := mul_le_mul_of_nonneg_right (le_of_lt hs) (norm_nonneg _)
    _ < 1 := by simpa using ht
  exact (ne_of_lt hlt) hnorm

private theorem separate_zero_slopes (i j : Fin 2) (hij : i ≠ j) :
    Separated (param i 0) (param j 0) := by
  have ho : IsOpen {s : ℂ | ‖s‖ < 1} := isOpen_lt continuous_norm continuous_const
  exact ⟨_,_,(param_isOpenEmbedding i).isOpenMap _ ho,
    (param_isOpenEmbedding j).isOpenMap _ ho,
    ⟨0,by simp,rfl⟩,⟨0,by simp,rfl⟩,small_slope_images_disjoint i j hij⟩

/-- Distinct projective points admit disjoint open neighbourhoods. -/
theorem points_separated (p q : Point) (hpq : p ≠ q) :
    ∃ U V : Set Point, IsOpen U ∧ IsOpen V ∧ p ∈ U ∧ q ∈ V ∧ Disjoint U V := by
  obtain ⟨i,s,rfl⟩ := charts_cover p
  obtain ⟨j,t,rfl⟩ := charts_cover q
  by_cases hij : i = j
  · subst j
    exact separate_same_chart i s t hpq
  by_cases hs : s = 0
  · by_cases ht : t = 0
    · subst s; subst t
      exact separate_zero_slopes i j hij
    · have ht' : t ∈ overlap j i := by simpa [overlap,Ne.symm hij] using ht
      rw [param_transition j i t ht'] at hpq ⊢
      exact separate_same_chart i _ _ hpq
  · have hs' : s ∈ overlap i j := by simpa [overlap,hij] using hs
    rw [param_transition i j s hs'] at hpq ⊢
    exact separate_same_chart j _ _ hpq

instance instT2SpacePoint : T2Space Point where
  t2 := points_separated

/-- The compact closed unit disc used to cover both affine charts. -/
def unitDisc : Set ℂ := {s | ‖s‖ ≤ 1}

theorem unitDisc_eq_closedBall : unitDisc = Metric.closedBall (0 : ℂ) 1 := by
  ext s
  simp [unitDisc,Metric.mem_closedBall,dist_zero_right]

theorem unitDisc_isCompact : IsCompact unitDisc := by
  rw [unitDisc_eq_closedBall]
  exact isCompact_closedBall (0 : ℂ) 1

/-- A slope outside the unit disc has reciprocal inside it. -/
theorem reciprocal_norm_le_one (s : ℂ) (hs : ¬ ‖s‖ ≤ 1) : ‖s⁻¹‖ ≤ 1 := by
  rw [norm_inv]
  exact (inv_le_one₀ (lt_trans zero_lt_one (lt_of_not_ge hs))).mpr (le_of_lt (lt_of_not_ge hs))

/-- Every projective point lies in one of the two closed affine unit discs. -/
theorem bounded_charts_cover (p : Point) : ∃ i s, p = param i s ∧ ‖s‖ ≤ 1 := by
  obtain ⟨i,s,rfl⟩ := charts_cover p
  by_cases hs : ‖s‖ ≤ 1
  · exact ⟨i,s,rfl,hs⟩
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  fin_cases i
  · exact ⟨1,s⁻¹,Blowup.lineX_eq_lineY_inv s hs0,reciprocal_norm_le_one s hs⟩
  · refine ⟨0,s⁻¹,?_,reciprocal_norm_le_one s hs⟩
    simpa using (Blowup.lineX_eq_lineY_inv s⁻¹ (inv_ne_zero hs0)).symm

theorem param_unitDisc_isCompact (i : Fin 2) : IsCompact (param i '' unitDisc) :=
  unitDisc_isCompact.image (param_continuous i)

/-- The explicit finite compact cover of the projective line. -/
theorem iUnion_param_unitDisc :
    (⋃ i : Fin 2, param i '' unitDisc) = (univ : Set Point) := by
  apply Set.eq_univ_of_forall
  intro p
  obtain ⟨i,s,hp,hs⟩ := bounded_charts_cover p
  exact Set.mem_iUnion.mpr ⟨i,s,hs,hp.symm⟩

theorem projectiveLine_isCompact : IsCompact (univ : Set Point) := by
  rw [← iUnion_param_unitDisc]
  exact isCompact_iUnion param_unitDisc_isCompact

instance instCompactSpacePoint : CompactSpace Point := ⟨projectiveLine_isCompact⟩

/-- Installing the projective topology preserves the existing incidence-atlas instance. -/
theorem blowup_topology_instance_unchanged :
    (inferInstance : TopologicalSpace Blowup.Point) = Blowup.instTopologicalSpacePoint := rfl

end FailureOfSemipositiveMetricExtension.ProjectiveLine
