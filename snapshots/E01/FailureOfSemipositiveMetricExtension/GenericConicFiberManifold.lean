import FailureOfSemipositiveMetricExtension.GenericConicFiberTopology

/-! The entire actual generic pencil fibre is a compact complex analytic curve.
Its two affine charts are transported along the verified projective-line
homeomorphism, and its inclusion into the original nearby surface is analytic. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil.Conic
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

variable (c : Data)

def fiberChart (i : Fin 2) : PartialHomeomorph (PencilFiber c) ℂ :=
  (fiberHomeomorph c).symm.toPartialHomeomorph.trans (FailureOfSemipositiveMetricExtension.ProjectiveLine.homeomorphChart i)

@[simp] theorem fiberChart_apply (i : Fin 2) (p : (PencilFiber c)) :
    fiberChart c i p = FailureOfSemipositiveMetricExtension.ProjectiveLine.coordinates i (fiberInverse c p) := rfl
@[simp] theorem fiberChart_symm_apply (i : Fin 2) (s : ℂ) :
    (fiberChart c i).symm s = fiberParam c (FailureOfSemipositiveMetricExtension.ProjectiveLine.param i s) := rfl
@[simp] theorem fiberChart_source (i : Fin 2) :
    (fiberChart c i).source = fiberInverse c ⁻¹' FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet i := by
  simp [fiberChart,PartialHomeomorph.trans_source]
  rfl
@[simp] theorem fiberChart_target (i : Fin 2) : (fiberChart c i).target = univ := by
  simp [fiberChart,PartialHomeomorph.trans_target]

theorem fiberCharts_cover (p : (PencilFiber c)) : ∃ i, p ∈ (fiberChart c i).source := by
  obtain ⟨i,s,hs⟩ := FailureOfSemipositiveMetricExtension.ProjectiveLine.charts_cover (fiberInverse c p)
  exact ⟨i,by rw [fiberChart_source c]; exact ⟨s,hs.symm⟩⟩

instance instChartedSpacePencilFiber : ChartedSpace ℂ (PencilFiber c) where
  atlas := range (fiberChart c)
  chartAt p := fiberChart c (Classical.choose (fiberCharts_cover c p))
  mem_chart_source p := Classical.choose_spec (fiberCharts_cover c p)
  chart_mem_atlas _ := ⟨_,rfl⟩

theorem fiberChart_mem_atlas (i : Fin 2) : fiberChart c i ∈ atlas ℂ (PencilFiber c) := ⟨i,rfl⟩

theorem fiberChart_transition_source (i j : Fin 2) :
    ((fiberChart c i).symm.trans (fiberChart c j)).source = FailureOfSemipositiveMetricExtension.ProjectiveLine.overlap i j := by
  ext s
  simp only [PartialHomeomorph.trans_source,PartialHomeomorph.symm_source,fiberChart_target c,
    Set.mem_inter_iff,Set.mem_univ,true_and,Set.mem_preimage,fiberChart_symm_apply c,
    fiberChart_source c,fiberInverse_param c,FailureOfSemipositiveMetricExtension.ProjectiveLine.param_mem_chartSet_iff]

theorem fiberChart_transition_apply (i j : Fin 2) (s : ℂ)
    (hs : s ∈ FailureOfSemipositiveMetricExtension.ProjectiveLine.overlap i j) :
    ((fiberChart c i).symm.trans (fiberChart c j)) s = FailureOfSemipositiveMetricExtension.ProjectiveLine.transition i j s := by
  change FailureOfSemipositiveMetricExtension.ProjectiveLine.coordinates j
    (fiberInverse c (fiberParam c (FailureOfSemipositiveMetricExtension.ProjectiveLine.param i s))) = _
  rw [fiberInverse_param c]
  exact FailureOfSemipositiveMetricExtension.ProjectiveLine.coordinates_transition i j s hs

instance instIsManifoldPencilFiber (n : WithTop ℕ∞) : IsManifold 𝓘(ℂ) n (PencilFiber c) := by
  apply isManifold_of_contDiffOn
  rintro u v ⟨i,rfl⟩ ⟨j,rfl⟩
  rw [fiberChart_transition_source c]
  simpa using (FailureOfSemipositiveMetricExtension.ProjectiveLine.transition_contDiffOn i j n).congr (fiberChart_transition_apply c i j)

theorem fiberAffineParam_contMDiff (i : Fin 2) (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) n (fun s => fiberParam c (FailureOfSemipositiveMetricExtension.ProjectiveLine.param i s)) := by
  have h := contMDiffOn_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ)) (n := n) (fiberChart_mem_atlas c i))
  rw [fiberChart_target c] at h
  exact contMDiffOn_univ.mp h

theorem fiberCoordinates_contMDiffOn (i : Fin 2) (n : WithTop ℕ∞) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) n (fiberChart c i) (fiberChart c i).source :=
  contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas (fiberChart_mem_atlas c i))

theorem fiber_contMDiff_of_param {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N]
    (I : ModelWithCorners ℂ E H) (n : WithTop ℕ∞) {f : (PencilFiber c) → N}
    (h : ∀ i, ContMDiff 𝓘(ℂ) I n (fun s => f (fiberParam c (FailureOfSemipositiveMetricExtension.ProjectiveLine.param i s)))) :
    ContMDiff 𝓘(ℂ) I n f := by
  intro p
  obtain ⟨i,hp⟩ := fiberCharts_cover c p
  have hc := (fiberCoordinates_contMDiffOn c i n).contMDiffAt ((fiberChart c i).open_source.mem_nhds hp)
  apply ((h i).contMDiffAt.comp p hc).congr_of_eventuallyEq
  filter_upwards [(fiberChart c i).open_source.mem_nhds hp] with q hq
  exact congrArg f ((fiberChart c i).left_inv hq).symm

/-- The projective parametrization and its actual inverse are both analytic. -/
theorem fiberParam_contMDiff (n : WithTop ℕ∞) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) n (fiberParam c) := by
  intro d
  obtain ⟨i,s,rfl⟩ := FailureOfSemipositiveMetricExtension.ProjectiveLine.charts_cover d
  have hp : FailureOfSemipositiveMetricExtension.ProjectiveLine.param i s ∈ FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet i := ⟨s,rfl⟩
  have hc := (FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.coordinates_contMDiffOn i n).contMDiffAt
    ((FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet_isOpen i).mem_nhds hp)
  apply ((fiberAffineParam_contMDiff c i n).contMDiffAt.comp _ hc).congr_of_eventuallyEq
  filter_upwards [(FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet_isOpen i).mem_nhds hp] with d hd
  exact congrArg (fiberParam c) (FailureOfSemipositiveMetricExtension.ProjectiveLine.param_coordinates i d hd).symm

theorem fiberInverse_contMDiff (n : WithTop ℕ∞) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) n (fiberInverse c) := by
  apply fiber_contMDiff_of_param c
  intro i
  simpa only [fiberInverse_param c] using FailureOfSemipositiveMetricExtension.ProjectiveLine.param_contMDiff i n

/-- The original subtype inclusion is analytic in the new one-dimensional complex atlas. -/
theorem fiberInclusion_contMDiff (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) n (fun p : (PencilFiber c) => p.val) := by
  apply fiber_contMDiff_of_param c
  intro i
  exact (param_contMDiff c n).comp (FailureOfSemipositiveMetricExtension.ProjectiveLine.param_contMDiff i n)

/-- The inherited topology and genuine analytic curve structure require no hypotheses. -/
theorem pencilFiber_complex_analytic : IsManifold 𝓘(ℂ) ω (PencilFiber c) := inferInstance

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil.Conic
