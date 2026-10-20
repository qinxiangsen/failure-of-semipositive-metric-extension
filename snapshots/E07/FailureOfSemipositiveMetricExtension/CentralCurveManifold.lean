import FailureOfSemipositiveMetricExtension.CentralCurveAnalytic

/-! The actual closed zero locus of ℓ is a compact complex analytic curve.
Its two affine charts are transported along the verified projective-line
homeomorphism, and its inclusion into the original central surface is analytic. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

def curveChart (i : Fin 2) : PartialHomeomorph EllCurve ℂ :=
  lineCurveHomeomorph.symm.toPartialHomeomorph.trans (FailureOfSemipositiveMetricExtension.ProjectiveLine.homeomorphChart i)

@[simp] theorem curveChart_apply (i : Fin 2) (p : EllCurve) :
    curveChart i p = FailureOfSemipositiveMetricExtension.ProjectiveLine.coordinates i (lineCurveInverse p) := rfl
@[simp] theorem curveChart_symm_apply (i : Fin 2) (s : ℂ) :
    (curveChart i).symm s = lineCurveParam (FailureOfSemipositiveMetricExtension.ProjectiveLine.param i s) := rfl
@[simp] theorem curveChart_source (i : Fin 2) :
    (curveChart i).source = lineCurveInverse ⁻¹' FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet i := by
  simp [curveChart,PartialHomeomorph.trans_source]
  rfl
@[simp] theorem curveChart_target (i : Fin 2) : (curveChart i).target = univ := by
  simp [curveChart,PartialHomeomorph.trans_target]

theorem curveCharts_cover (p : EllCurve) : ∃ i, p ∈ (curveChart i).source := by
  obtain ⟨i,s,hs⟩ := FailureOfSemipositiveMetricExtension.ProjectiveLine.charts_cover (lineCurveInverse p)
  exact ⟨i,by rw [curveChart_source]; exact ⟨s,hs.symm⟩⟩

instance instChartedSpaceEllCurve : ChartedSpace ℂ EllCurve where
  atlas := range curveChart
  chartAt p := curveChart (Classical.choose (curveCharts_cover p))
  mem_chart_source p := Classical.choose_spec (curveCharts_cover p)
  chart_mem_atlas _ := ⟨_,rfl⟩

theorem curveChart_mem_atlas (i : Fin 2) : curveChart i ∈ atlas ℂ EllCurve := ⟨i,rfl⟩

theorem curveChart_transition_source (i j : Fin 2) :
    ((curveChart i).symm.trans (curveChart j)).source = FailureOfSemipositiveMetricExtension.ProjectiveLine.overlap i j := by
  ext s
  simp only [PartialHomeomorph.trans_source,PartialHomeomorph.symm_source,curveChart_target,
    Set.mem_inter_iff,Set.mem_univ,true_and,Set.mem_preimage,curveChart_symm_apply,
    curveChart_source,lineCurveInverse_param,FailureOfSemipositiveMetricExtension.ProjectiveLine.param_mem_chartSet_iff]

theorem curveChart_transition_apply (i j : Fin 2) (s : ℂ)
    (hs : s ∈ FailureOfSemipositiveMetricExtension.ProjectiveLine.overlap i j) :
    ((curveChart i).symm.trans (curveChart j)) s = FailureOfSemipositiveMetricExtension.ProjectiveLine.transition i j s := by
  change FailureOfSemipositiveMetricExtension.ProjectiveLine.coordinates j
    (lineCurveInverse (lineCurveParam (FailureOfSemipositiveMetricExtension.ProjectiveLine.param i s))) = _
  rw [lineCurveInverse_param]
  exact FailureOfSemipositiveMetricExtension.ProjectiveLine.coordinates_transition i j s hs

instance instIsManifoldEllCurve (n : WithTop ℕ∞) : IsManifold 𝓘(ℂ) n EllCurve := by
  apply isManifold_of_contDiffOn
  rintro c c' ⟨i,rfl⟩ ⟨j,rfl⟩
  rw [curveChart_transition_source]
  simpa using (FailureOfSemipositiveMetricExtension.ProjectiveLine.transition_contDiffOn i j n).congr (curveChart_transition_apply i j)

theorem curveAffineParam_contMDiff (i : Fin 2) (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) n (fun s => lineCurveParam (FailureOfSemipositiveMetricExtension.ProjectiveLine.param i s)) := by
  have h := contMDiffOn_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ)) (n := n) (curveChart_mem_atlas i))
  rw [curveChart_target] at h
  exact contMDiffOn_univ.mp h

theorem curveCoordinates_contMDiffOn (i : Fin 2) (n : WithTop ℕ∞) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) n (curveChart i) (curveChart i).source :=
  contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas (curveChart_mem_atlas i))

theorem curve_contMDiff_of_param {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N]
    (I : ModelWithCorners ℂ E H) (n : WithTop ℕ∞) {f : EllCurve → N}
    (h : ∀ i, ContMDiff 𝓘(ℂ) I n (fun s => f (lineCurveParam (FailureOfSemipositiveMetricExtension.ProjectiveLine.param i s)))) :
    ContMDiff 𝓘(ℂ) I n f := by
  intro p
  obtain ⟨i,hp⟩ := curveCharts_cover p
  have hc := (curveCoordinates_contMDiffOn i n).contMDiffAt ((curveChart i).open_source.mem_nhds hp)
  apply ((h i).contMDiffAt.comp p hc).congr_of_eventuallyEq
  filter_upwards [(curveChart i).open_source.mem_nhds hp] with q hq
  exact congrArg f ((curveChart i).left_inv hq).symm

/-- The projective parametrization and its actual inverse are both analytic. -/
theorem lineCurveParam_contMDiff (n : WithTop ℕ∞) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) n lineCurveParam := by
  intro d
  obtain ⟨i,s,rfl⟩ := FailureOfSemipositiveMetricExtension.ProjectiveLine.charts_cover d
  have hp : FailureOfSemipositiveMetricExtension.ProjectiveLine.param i s ∈ FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet i := ⟨s,rfl⟩
  have hc := (FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.coordinates_contMDiffOn i n).contMDiffAt
    ((FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet_isOpen i).mem_nhds hp)
  apply ((curveAffineParam_contMDiff i n).contMDiffAt.comp _ hc).congr_of_eventuallyEq
  filter_upwards [(FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet_isOpen i).mem_nhds hp] with d hd
  exact congrArg lineCurveParam (FailureOfSemipositiveMetricExtension.ProjectiveLine.param_coordinates i d hd).symm

theorem lineCurveInverse_contMDiff (n : WithTop ℕ∞) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) n lineCurveInverse := by
  apply curve_contMDiff_of_param
  intro i
  simpa only [lineCurveInverse_param] using FailureOfSemipositiveMetricExtension.ProjectiveLine.param_contMDiff i n

/-- The original subtype inclusion is analytic in the new one-dimensional complex atlas. -/
theorem curveInclusion_contMDiff (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) n (fun p : EllCurve => p.val) := by
  apply curve_contMDiff_of_param
  intro i
  exact (lineParam_contMDiff n).comp (FailureOfSemipositiveMetricExtension.ProjectiveLine.param_contMDiff i n)

/-- The inherited topology and genuine analytic curve structure require no hypotheses. -/
theorem ellCurve_complex_analytic : IsManifold 𝓘(ℂ) ω EllCurve := inferInstance

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
