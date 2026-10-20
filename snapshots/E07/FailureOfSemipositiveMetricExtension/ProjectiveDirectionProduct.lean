import FailureOfSemipositiveMetricExtension.GlobalAnalyticMaps

/-! The actual finite product of the four projective direction spaces, with its
original product topology and the standard sixteen affine analytic charts. -/
namespace FailureOfSemipositiveMetricExtension.ProjectiveDirectionProduct
noncomputable section
open Set Topology IsManifold
open scoped Manifold ContDiff

abbrev Point := Fin 4 → ProjectiveLine.Point
abbrev Coord := Fin 4 → ℂ
abbrev Index := Fin 4 → Fin 2

def chart (i : Index) : PartialHomeomorph Point Coord :=
  PartialHomeomorph.pi (fun r => ProjectiveLine.homeomorphChart (i r))

def param (i : Index) (q : Coord) : Point := fun r => ProjectiveLine.param (i r) (q r)

def coordinates (i : Index) (p : Point) : Coord := fun r => ProjectiveLine.coordinates (i r) (p r)

@[simp] theorem chart_apply (i : Index) (p : Point) : chart i p = coordinates i p := rfl
@[simp] theorem chart_symm_apply (i : Index) (q : Coord) : (chart i).symm q = param i q := rfl
@[simp] theorem chart_source (i : Index) :
    (chart i).source = {p | ∀ r, p r ∈ ProjectiveLine.chartSet (i r)} := by
  ext p
  simp [chart]
@[simp] theorem chart_target (i : Index) : (chart i).target = univ := by
  simp [chart]

theorem charts_cover (p : Point) : ∃ i, p ∈ (chart i).source := by
  let i : Index := fun r => Classical.choose (ProjectiveLine.charts_cover (p r))
  refine ⟨i,?_⟩
  rw [chart_source]
  intro r
  obtain ⟨s,hs⟩ := Classical.choose_spec (ProjectiveLine.charts_cover (p r))
  exact ⟨s,hs.symm⟩

instance instChartedSpacePoint : ChartedSpace Coord Point where
  atlas := range chart
  chartAt p := chart (Classical.choose (charts_cover p))
  mem_chart_source p := Classical.choose_spec (charts_cover p)
  chart_mem_atlas _ := ⟨_,rfl⟩

theorem chart_mem_atlas (i : Index) : chart i ∈ atlas Coord Point := ⟨i,rfl⟩

theorem chart_transition_source (i j : Index) :
    ((chart i).symm.trans (chart j)).source =
      {q | ∀ r, q r ∈ ProjectiveLine.overlap (i r) (j r)} := by
  ext q
  simp [PartialHomeomorph.trans_source,param]

theorem chart_transition_apply (i j : Index) (q : Coord)
    (hq : q ∈ ((chart i).symm.trans (chart j)).source) (r : Fin 4) :
    ((chart i).symm.trans (chart j)) q r = ProjectiveLine.transition (i r) (j r) (q r) := by
  apply ProjectiveLine.coordinates_transition
  exact (chart_transition_source i j ▸ hq) r

instance instIsManifoldPoint (n : WithTop ℕ∞) : IsManifold 𝓘(ℂ,Coord) n Point := by
  apply isManifold_of_contDiffOn
  rintro u v ⟨i,rfl⟩ ⟨j,rfl⟩
  suffices h : ContDiffOn ℂ n ((chart i).symm.trans (chart j))
      ((chart i).symm.trans (chart j)).source by simpa using h
  apply contDiffOn_pi.mpr
  intro r
  have h := (ProjectiveLine.transition_contDiffOn (i r) (j r) n).comp
    (contDiff_apply ℂ ℂ r).contDiffOn
    (fun q (hq : q ∈ ((chart i).symm.trans (chart j)).source) =>
      (chart_transition_source i j ▸ hq) r)
  exact h.congr (fun q hq => chart_transition_apply i j q hq r)

theorem param_contMDiff (i : Index) (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ,Coord) 𝓘(ℂ,Coord) n (param i) := by
  have h := contMDiffOn_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ,Coord)) (n := n) (chart_mem_atlas i))
  rw [chart_target] at h
  exact contMDiffOn_univ.mp h

theorem coordinates_contMDiffOn (i : Index) (n : WithTop ℕ∞) :
    ContMDiffOn 𝓘(ℂ,Coord) 𝓘(ℂ,Coord) n (coordinates i) (chart i).source :=
  contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas (chart_mem_atlas i))

theorem contMDiff_of_param {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N]
    (I : ModelWithCorners ℂ E H) (n : WithTop ℕ∞) {f : Point → N}
    (h : ∀ i, ContMDiff 𝓘(ℂ,Coord) I n (f ∘ param i)) :
    ContMDiff 𝓘(ℂ,Coord) I n f := by
  intro p
  obtain ⟨i,hp⟩ := charts_cover p
  have hc := (coordinates_contMDiffOn i n).contMDiffAt ((chart i).open_source.mem_nhds hp)
  apply ((h i).contMDiffAt.comp p hc).congr_of_eventuallyEq
  filter_upwards [(chart i).open_source.mem_nhds hp] with q hq
  exact congrArg f ((chart i).left_inv hq).symm

theorem eval_contMDiff (r : Fin 4) (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ,Coord) 𝓘(ℂ) n (fun p : Point => p r) := by
  apply contMDiff_of_param
  intro i
  exact (ProjectiveLine.param_contMDiff (i r) n).comp (contDiff_apply ℂ ℂ r).contMDiff

/-- Analyticity into the actual product is equivalent to componentwise
analyticity; the proof uses its sixteen standard affine charts. -/
theorem contMDiffAt_of_components {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℂ E H) (n : WithTop ℕ∞) {f : M → Point} {p : M}
    (hf : ∀ r, ContMDiffAt I 𝓘(ℂ) n (fun q => f q r) p) :
    ContMDiffAt I 𝓘(ℂ,Coord) n f p := by
  obtain ⟨i,hp⟩ := charts_cover (f p)
  have hc : ContinuousAt f p := continuousAt_pi.mpr (fun r => (hf r).continuousAt)
  have hcoord : ContMDiffAt I 𝓘(ℂ,Coord) n (fun q => coordinates i (f q)) p := by
    apply contMDiffAt_pi_space.mpr
    intro r
    exact ((GlobalIncidence.lineCoordinates_contMDiffOn (i r) n).contMDiffAt
      ((ProjectiveLine.chartSet_isOpen (i r)).mem_nhds
        ((chart_source i ▸ hp) r))).comp p (hf r)
  apply ((param_contMDiff i n).contMDiffAt.comp p hcoord).congr_of_eventuallyEq
  filter_upwards [hc.preimage_mem_nhds ((chart i).open_source.mem_nhds hp)] with q hq
  exact ((chart i).left_inv hq).symm

theorem contMDiff_of_components {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℂ E H) (n : WithTop ℕ∞) {f : M → Point}
    (hf : ∀ r, ContMDiff I 𝓘(ℂ) n (fun q => f q r)) :
    ContMDiff I 𝓘(ℂ,Coord) n f :=
  fun _ => contMDiffAt_of_components I n (fun r => (hf r).contMDiffAt)

/-- The supplied topology is exactly the existing finite product topology. -/
theorem topology_is_product : (inferInstance : TopologicalSpace Point) =
    Pi.topologicalSpace := rfl

end
end FailureOfSemipositiveMetricExtension.ProjectiveDirectionProduct
