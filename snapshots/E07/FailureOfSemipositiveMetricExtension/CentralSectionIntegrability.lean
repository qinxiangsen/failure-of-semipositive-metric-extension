import FailureOfSemipositiveMetricExtension.CentralSectionDensity

/-! Actual Lebesgue integrability of the prescribed section's weighted local
coefficients in the genuine two-complex-dimensional charts. The remaining
canonical-bundle and global adjoint interpretation is not assumed. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold MeasureTheory
open scoped Manifold ContDiff

theorem complex_coordinate_hyperplane_null :
    (volume : Measure FixedFiber.Coord) {q | q.2 = 0} = 0 := by
  rw [show {q : FixedFiber.Coord | q.2 = 0} = univ ×ˢ ({0} : Set ℂ) by ext q; simp]
  rw [Measure.volume_eq_prod,Measure.prod_prod]
  simp

theorem sigmaRegularDensity_integrableOn_compact_chart (i : Index) (r : Fin 4) (e : Fin 2)
    (K : Set FixedFiber.Coord) (hK : IsCompact K)
    (hd : K ⊆ FixedFiber.domain 0 r e)
    (hf : MapsTo (FixedFiber.param 0 r e) K (baseSet 0 i)) :
    IntegrableOn (fun q => sigmaRegularDensity i (FixedFiber.param 0 r e q)) K volume := by
  have hc := (sigmaRegularDensity_contMDiffOn i).continuousOn.comp
    ((FixedFiber.param_contMDiffOn 0 r e 0).continuousOn.mono hd) hf
  exact hc.integrableOn_compact hK

/-- The original weighted density is integrable, not just its canceled expression.
The actual singular set is proved to lie in a null complex coordinate hyperplane. -/
theorem sigmaWeightedDensity_integrableOn_compact_chart (i : Index) (r : Fin 4) (e : Fin 2)
    (K : Set FixedFiber.Coord) (hK : IsCompact K)
    (hd : K ⊆ FixedFiber.domain 0 r e)
    (hf : MapsTo (FixedFiber.param 0 r e) K (baseSet 0 i)) :
    IntegrableOn (fun q => sigmaWeightedDensity i (FixedFiber.param 0 r e q)) K volume := by
  apply (sigmaRegularDensity_integrableOn_compact_chart i r e K hK hd hf).congr_fun_ae
  have hn : ∀ᵐ q : FixedFiber.Coord, q.2 ≠ 0 := by
    simpa only [ae_iff,not_not] using complex_coordinate_hyperplane_null
  filter_upwards [ae_restrict_of_ae hn,ae_restrict_mem hK.measurableSet] with q hq hqK
  symm
  apply sigmaWeightedDensity_eq_regular i (FixedFiber.param 0 r e q) (hf hqK)
  intro heq
  have hz : sectionValue ellSection (FixedFiber.param 0 r e q) = 0 :=
    (sectionValue_zero_iff ellSection i _ (hf hqK)).mpr heq
  exact hq ((ellSection_zero_iff_param r e q (hd hqK)).mp hz).2.2

/-- Every actual central point has a positive-radius coordinate neighbourhood
on which the genuine fourth-power weighted coefficient is Lebesgue integrable. -/
theorem sigmaWeightedDensity_locally_integrable (p : Fiber 0) :
    ∃ (r : Fin 4) (e : Fin 2) (i : Index) (q : FixedFiber.Coord) (ε : ℝ),
      0 < ε ∧ FixedFiber.param 0 r e q = p ∧
      Metric.closedBall q ε ⊆ FixedFiber.domain 0 r e ∧
      MapsTo (FixedFiber.param 0 r e) (Metric.closedBall q ε) (baseSet 0 i) ∧
      IntegrableOn (fun z => sigmaWeightedDensity i (FixedFiber.param 0 r e z))
        (Metric.closedBall q ε) volume := by
  obtain ⟨⟨r,e⟩,hp⟩ := FixedFiber.charts_cover 0 p
  let i := (core 0 (-7) (fun _ => 3)).indexAt p
  have hi : p ∈ baseSet 0 i := (core 0 (-7) (fun _ => 3)).mem_baseSet_at p
  let q := FixedFiber.coordinates 0 r e p
  have hq : q ∈ FixedFiber.domain 0 r e := (FixedFiber.chart 0 r e).map_source hp
  have heq : FixedFiber.param 0 r e q = p := FixedFiber.param_coordinates 0 r e p hp
  have hU : IsOpen (FixedFiber.domain 0 r e ∩ FixedFiber.param 0 r e ⁻¹' baseSet 0 i) :=
    (FixedFiber.chart 0 r e).isOpen_inter_preimage_symm (baseSet_isOpen 0 i)
  have hqU : q ∈ FixedFiber.domain 0 r e ∩ FixedFiber.param 0 r e ⁻¹' baseSet 0 i :=
    ⟨hq,by change FixedFiber.param 0 r e q ∈ baseSet 0 i; rw [heq]; exact hi⟩
  obtain ⟨ε,hε,hεU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hqU)
  have hd : Metric.closedBall q ε ⊆ FixedFiber.domain 0 r e := fun z hz => (hεU hz).1
  have hf : MapsTo (FixedFiber.param 0 r e) (Metric.closedBall q ε) (baseSet 0 i) :=
    fun z hz => (hεU hz).2
  exact ⟨r,e,i,q,ε,hε,heq,hd,hf,
    sigmaWeightedDensity_integrableOn_compact_chart i r e (Metric.closedBall q ε)
      (isCompact_closedBall q ε) hd hf⟩

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
