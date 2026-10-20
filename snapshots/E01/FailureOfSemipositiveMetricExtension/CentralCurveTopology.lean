import FailureOfSemipositiveMetricExtension.CentralRationalCurve

/-! The genuine projective line is homeomorphic to the actual closed zero locus
of ℓ with its inherited topology.  The latter is therefore a compact Hausdorff
second-countable curve; its complex atlas is constructed separately. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

theorem lineBase_contMDiff (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ,ℂ × ℂ) n lineBase := by
  intro d
  obtain ⟨i,s,rfl⟩ := FailureOfSemipositiveMetricExtension.ProjectiveLine.charts_cover d
  have hp : FailureOfSemipositiveMetricExtension.ProjectiveLine.param i s ∈ FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet i := ⟨s,rfl⟩
  have hc := (FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.coordinates_contMDiffOn i n).contMDiffAt
    ((FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet_isOpen i).mem_nhds hp)
  have hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ,ℂ × ℂ) n
      (fun z : ℂ => FailureOfSemipositiveMetricExtension.ProjectivePlane.param i.castSucc (z,0)) :=
    (FailureOfSemipositiveMetricExtension.ProjectivePlane.param_contMDiff i.castSucc n).comp
      (contDiff_id.prodMk contDiff_const).contMDiff
  apply (hf.contMDiffAt.comp _ hc).congr_of_eventuallyEq
  filter_upwards [(FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet_isOpen i).mem_nhds hp] with d hd
  change lineBase d = FailureOfSemipositiveMetricExtension.ProjectivePlane.param i.castSucc (FailureOfSemipositiveMetricExtension.ProjectiveLine.coordinates i d,0)
  rw [← lineBase_param,FailureOfSemipositiveMetricExtension.ProjectiveLine.param_coordinates i d hd]

theorem lineBase_continuous : Continuous lineBase := (lineBase_contMDiff 0).continuous

theorem lineDirections_continuous : Continuous lineDirections := by
  apply continuous_pi
  intro r
  by_cases hr : r = 3
  · simpa [lineDirections,hr] using (continuous_id : Continuous (id : Direction → Direction))
  · simpa [lineDirections,hr] using (continuous_const : Continuous (fun _ : Direction => FailureOfSemipositiveMetricExtension.ProjectiveLine.param 0 0))

theorem lineParam_continuous : Continuous lineParam :=
  (lineBase_continuous.prodMk lineDirections_continuous).subtype_mk _

instance instTopologicalSpaceEllCurve : TopologicalSpace EllCurve :=
  inferInstanceAs (TopologicalSpace {p : Fiber 0 // sectionValue ellSection p = 0})

/-- The curve topology is literally the induced topology of its original fibre inclusion. -/
theorem ellCurve_topology_is_subspace : instTopologicalSpaceEllCurve =
    TopologicalSpace.induced (fun p : EllCurve => p.val) (inferInstance : TopologicalSpace (Fiber 0)) := rfl

theorem lineCurveParam_continuous : Continuous lineCurveParam := lineParam_continuous.subtype_mk _

theorem lineCurveInverse_continuous : Continuous lineCurveInverse :=
  (FixedFiber.direction_contMDiff 0 3 0).continuous.comp continuous_subtype_val

/-- Actual projective-line homeomorphism, preserving the original zero-locus topology. -/
def lineCurveHomeomorph : Direction ≃ₜ EllCurve where
  toEquiv := lineCurveEquiv
  continuous_toFun := lineCurveParam_continuous
  continuous_invFun := lineCurveInverse_continuous

instance instCompactSpaceEllCurve : CompactSpace EllCurve :=
  isCompact_iff_compactSpace.mp ellZeroSet_isClosed.isCompact

instance instT2SpaceEllCurve : T2Space EllCurve :=
  inferInstanceAs (T2Space {p : Fiber 0 // sectionValue ellSection p = 0})

instance instSecondCountableTopologyEllCurve : SecondCountableTopology EllCurve :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology

theorem lineParam_isClosedEmbedding : IsClosedEmbedding lineParam :=
  lineParam_continuous.isClosedEmbedding lineParam_injective

theorem lineParam_range : Set.range lineParam = {p : Fiber 0 | sectionValue ellSection p = 0} := by
  ext p
  constructor
  · rintro ⟨d,rfl⟩
    exact ellSection_lineParam_zero d
  · exact lineParam_surjective_zero p

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
