import FailureOfSemipositiveMetricExtension.GeneralAdjointChartDensity

/-! Actual arbitrary-dimensional chart-change derivatives and their inverses. -/
namespace FailureOfSemipositiveMetricExtension.GeneralMultiplier.AnalyticCoordinate
noncomputable section
open Set IsManifold
open scoped Manifold ContDiff

variable {n : ℕ} {N : Type} [TopologicalSpace N] [ChartedSpace (Coord n) N]
    [IsManifold 𝓘(ℂ,Coord n) ω N]

protected theorem mdifferentiable (e : AnalyticCoordinate n N) :
    e.chart.MDifferentiable 𝓘(ℂ,Coord n) 𝓘(ℂ,Coord n) :=
  ⟨e.forward.mdifferentiableOn (by simp),e.inverse.mdifferentiableOn (by simp)⟩

def change (e f : AnalyticCoordinate n N) : Coord n → Coord n := f.chart ∘ e.chart.symm

def changeDomain (e f : AnalyticCoordinate n N) : Set (Coord n) :=
  e.chart.target ∩ e.chart.symm ⁻¹' f.chart.source

theorem changeDomain_open (e f : AnalyticCoordinate n N) : IsOpen (changeDomain e f) :=
  e.chart.symm.isOpen_inter_preimage f.chart.open_source

theorem change_contDiffOn (e f : AnalyticCoordinate n N) :
    ContDiffOn ℂ ω (change e f) (changeDomain e f) := by
  apply contMDiffOn_iff_contDiffOn.mp
  exact f.forward.comp (e.inverse.mono inter_subset_left) (fun _ h => h.2)

theorem change_differentiableAt (e f : AnalyticCoordinate n N) {q : Coord n}
    (hq : q ∈ changeDomain e f) : DifferentiableAt ℂ (change e f) q :=
  ((change_contDiffOn e f).contDiffAt ((changeDomain_open e f).mem_nhds hq)).differentiableAt (by simp)

theorem change_injOn (e f : AnalyticCoordinate n N) : InjOn (change e f) (changeDomain e f) :=
  fun _ hp _ hq h => e.chart.symm.injOn hp.1 hq.1 (f.chart.injOn hp.2 hq.2 h)

theorem change_mem_reverse (e f : AnalyticCoordinate n N) {q : Coord n}
    (hq : q ∈ changeDomain e f) : change e f q ∈ changeDomain f e := by
  refine ⟨f.chart.map_source hq.2,?_⟩
  change f.chart.symm (f.chart (e.chart.symm q)) ∈ e.chart.source
  rw [f.chart.left_inv hq.2]
  exact e.chart.map_target hq.1

theorem change_inverse (e f : AnalyticCoordinate n N) {q : Coord n}
    (hq : q ∈ changeDomain e f) : change f e (change e f q) = q := by
  change e.chart (f.chart.symm (f.chart (e.chart.symm q))) = q
  rw [f.chart.left_inv hq.2,e.chart.right_inv hq.1]

theorem change_jacobian_inverse (e f : AnalyticCoordinate n N) {q : Coord n}
    (hq : q ∈ changeDomain e f) :
    GeneralComplexJacobian.jacobian (change f e) (change e f q) *
      GeneralComplexJacobian.jacobian (change e f) q = 1 := by
  rw [← GeneralComplexJacobian.jacobian_comp q (change_differentiableAt e f hq)
    (change_differentiableAt f e (change_mem_reverse e f hq))]
  have heq : (change f e ∘ change e f) =ᶠ[nhds q] id :=
    Filter.mem_of_superset ((changeDomain_open e f).mem_nhds hq) (fun _ h => change_inverse e f h)
  unfold GeneralComplexJacobian.jacobian
  rw [heq.fderiv_eq]
  exact GeneralComplexJacobian.jacobian_id q

theorem change_jacobian_continuousOn (e f : AnalyticCoordinate n N) :
    ContinuousOn (GeneralComplexJacobian.jacobian (change e f)) (changeDomain e f) :=
  ContinuousLinearMap.continuous_det.comp_continuousOn
    ((change_contDiffOn e f).continuousOn_fderiv_of_isOpen (changeDomain_open e f) (by simp))

theorem reverseJacobian_eq (e f : AnalyticCoordinate n N) (p : N)
    (he : p ∈ e.chart.source) (hf : p ∈ f.chart.source) :
    GeneralCao.CentralAdjointSection.reverseJacobian e f p =
      GeneralComplexJacobian.jacobian (change f e) (f.chart p) := by
  have hc := mfderiv_comp (f.chart p)
    (show MDifferentiableAt 𝓘(ℂ,Coord n) 𝓘(ℂ,Coord n) e.chart (f.chart.symm (f.chart p)) by
      rw [f.chart.left_inv hf]; exact e.mdifferentiable.mdifferentiableAt he)
    (f.mdifferentiable.mdifferentiableAt_symm (f.chart.map_source hf))
  rw [f.chart.left_inv hf,mfderiv_eq_fderiv] at hc
  unfold GeneralCao.CentralAdjointSection.reverseJacobian GeneralComplexJacobian.jacobian change
  rw [hc]

end
end FailureOfSemipositiveMetricExtension.GeneralMultiplier.AnalyticCoordinate
