import FailureOfSemipositiveMetricExtension.CentralCurveTopology

/-! The explicit projective-line parametrization is complex analytic as a map
into the original two-dimensional central fibre, including at exceptional points. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

def lineRadius (r : Fin 4) (d : Direction) : ℂ :=
  if r = 2 then (FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates (baseChart r) (lineBase d)).1 - 1
  else (FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates (baseChart r) (lineBase d)).1

def lineLocalCoord (r : Fin 4) (d : Direction) : FixedFiber.Coord := (lineRadius r d,0)

def lineChartSource (r : Fin 4) : Set Direction := lineParam ⁻¹' FixedFiber.source 0 r 0

theorem lineChartSource_isOpen (r : Fin 4) : IsOpen (lineChartSource r) :=
  (FixedFiber.source_isOpen 0 r 0).preimage lineParam_continuous

theorem lineRadius_eq (r : Fin 4) (d : Direction) (hd : d ∈ lineChartSource r) :
    lineRadius r d = (FixedFiber.coordinates 0 r 0 (lineParam d)).1 := by
  have hq := FixedFiber.param_coordinates 0 r 0 (lineParam d) hd
  have hb := congrArg (FixedFiber.blowdown 0) hq
  change affineBase r 0 (Blowup.projection (localParam 0 (FixedFiber.coordinates 0 r 0 (lineParam d)))) = lineBase d at hb
  unfold lineRadius
  rw [← hb,affineBase_eq_param,FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates_param]
  fin_cases r <;> simp [baseCoordinates,localParam,Blowup.projection,Blowup.X]

theorem lineLocalCoord_eq (r : Fin 4) (d : Direction) (hd : d ∈ lineChartSource r) :
    lineLocalCoord r d = FixedFiber.coordinates 0 r 0 (lineParam d) := by
  apply Prod.ext
  · exact lineRadius_eq r d hd
  · exact (lineParam_chart_data d r 0 hd).2.2.symm

theorem lineLocalCoord_contMDiffOn (r : Fin 4) (n : WithTop ℕ∞) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) n (lineLocalCoord r) (lineChartSource r) := by
  have hc : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ,ℂ × ℂ) n
      (fun d => FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates (baseChart r) (lineBase d))
      (lineChartSource r) :=
    (FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle.coordinates_contMDiffOn (baseChart r) n).comp
      (lineBase_contMDiff n).contMDiffOn
      (fun d hd => ((mem_chartSource_iff r 0 (FixedFiber.inclusion 0 (lineParam d))).mp hd).1)
  have hfirst := (contDiff_fst (𝕜 := ℂ) (n := n)).contMDiff.comp_contMDiffOn hc
  have hr : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) n (lineRadius r) (lineChartSource r) := by
    change ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) n (fun d => lineRadius r d) (lineChartSource r)
    by_cases h : r = 2
    · have hsub : ContDiff ℂ n (fun z : ℂ => z-1) := contDiff_id.sub contDiff_const
      simpa only [lineRadius,if_pos h,Function.comp_apply] using hsub.contMDiff.comp_contMDiffOn hfirst
    · simpa only [lineRadius,if_neg h,Function.comp_apply] using hfirst
  exact hr.prodMk_space contMDiffOn_const

/-- Actual analyticity in the already-constructed complex surface structure. -/
theorem lineParam_contMDiff (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) n lineParam := by
  intro d
  obtain ⟨⟨r,e⟩,hp⟩ := FixedFiber.charts_cover 0 (lineParam d)
  have he := (lineParam_chart_data d r e hp).2.1
  subst e
  have hd : d ∈ lineChartSource r := hp
  have hq : lineLocalCoord r d ∈ FixedFiber.domain 0 r 0 := by
    rw [lineLocalCoord_eq r d hd]
    exact (FixedFiber.chart 0 r 0).map_source hp
  have hf := (FixedFiber.param_contMDiffOn 0 r 0 n).contMDiffAt
    ((FixedFiber.domain_isOpen 0 r 0).mem_nhds hq)
  have hg := (lineLocalCoord_contMDiffOn r n).contMDiffAt ((lineChartSource_isOpen r).mem_nhds hd)
  apply (hf.comp d hg).congr_of_eventuallyEq
  filter_upwards [(lineChartSource_isOpen r).mem_nhds hd] with d' hd'
  change lineParam d' = FixedFiber.param 0 r 0 (lineLocalCoord r d')
  rw [lineLocalCoord_eq r d' hd',FixedFiber.param_coordinates 0 r 0 (lineParam d') hd']

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
