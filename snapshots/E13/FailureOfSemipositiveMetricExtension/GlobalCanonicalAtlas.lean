import FailureOfSemipositiveMetricExtension.GlobalCanonicalJacobian

/-! The actual total-space canonical line bundle, glued from genuine ordered
threefold Jacobian determinants. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalCanonical
noncomputable section
open Set Bundle Topology
open scoped Manifold ContDiff

abbrev Index := Fin 4 × Fin 2

theorem charts_cover (p : Total) : ∃ i : Index, p ∈ chartSource i.1 i.2 := by
  obtain ⟨i,e,q,hq,hp⟩ := global_charts_cover p
  exact ⟨(i,e),q,hq,hp.symm⟩

def chartIndex (p : Total) : Index := Classical.choose (charts_cover p)

theorem chartIndex_mem_source (p : Total) : p ∈ chartSource (chartIndex p).1 (chartIndex p).2 :=
  Classical.choose_spec (charts_cover p)

def chartJacobian (i j : Fin 4) (e f : Fin 2) (p : Total) : ℂ :=
  ComplexThreefoldJacobian.jacobian (change i j e f) (chartCoordinates i e p)

theorem coordinates_mem_changeDomain (i j : Fin 4) (e f : Fin 2) (p : Total)
    (hi : p ∈ chartSource i e) (hj : p ∈ chartSource j f) :
    chartCoordinates i e p ∈ changeDomain i j e f := by
  refine ⟨(homeomorphChart i e).map_source hi,?_⟩
  change chartParam i e (chartCoordinates i e p) ∈ chartSource j f
  rwa [chartParam_coordinates i e p hi]

theorem chartJacobian_contMDiffOn (i j : Fin 4) (e f : Fin 2) :
    ContMDiffOn 𝓘(ℂ,ChartCoord) 𝓘(ℂ) ω (chartJacobian i j e f)
      (chartSource i e ∩ chartSource j f) :=
  (ComplexThreefoldJacobian.jacobian_contDiffOn (change_contDiffOn i j e f ω)
    (changeDomain_isOpen i j e f)).contMDiffOn.comp
      ((chartCoordinates_contMDiffOn i e ω).mono inter_subset_left)
      (fun p hp => coordinates_mem_changeDomain i j e f p hp.1 hp.2)

@[simp] theorem chartJacobian_self (i : Fin 4) (e : Fin 2) (p : Total) :
    chartJacobian i i e e p = 1 := by
  have h : change i i e e = id := funext (chartCoordinates_param i e)
  simp [chartJacobian,h]

theorem chartJacobian_cocycle (i j k : Fin 4) (e f g : Fin 2) (p : Total)
    (hi : p ∈ chartSource i e) (hj : p ∈ chartSource j f) (hk : p ∈ chartSource k g) :
    chartJacobian j k f g p * chartJacobian i j e f p = chartJacobian i k e g p := by
  let q := chartCoordinates i e p
  have hq : q ∈ changeDomain i j e f := coordinates_mem_changeDomain i j e f p hi hj
  have hc : change i j e f q = chartCoordinates j f p := by
    change chartCoordinates j f (chartParam i e (chartCoordinates i e p)) = _
    rw [chartParam_coordinates i e p hi]
  have heq : (change j k f g ∘ change i j e f) =ᶠ[𝓝 q] change i k e g := by
    filter_upwards [(changeDomain_isOpen i j e f).mem_nhds hq] with w hw
    change chartCoordinates k g (chartParam j f (chartCoordinates j f (chartParam i e w))) = _
    have hp : chartParam i e w ∈ chartSource j f := hw.2
    rw [chartParam_coordinates j f (chartParam i e w) hp]
    rfl
  have h := congrArg ComplexThreefoldJacobian.determinant (heq.fderiv_eq (𝕜 := ℂ))
  change ComplexThreefoldJacobian.jacobian (change j k f g ∘ change i j e f) q =
    ComplexThreefoldJacobian.jacobian (change i k e g) q at h
  have hd : DifferentiableAt ℂ (change j k f g) (change i j e f q) := by
    rw [hc]
    exact change_differentiableAt j k f g _ (coordinates_mem_changeDomain j k f g p hj hk)
  rw [ComplexThreefoldJacobian.jacobian_comp q (change_differentiableAt i j e f q hq) hd,hc] at h
  exact h

theorem chartJacobian_ne_zero (i j : Fin 4) (e f : Fin 2) (p : Total)
    (hi : p ∈ chartSource i e) (hj : p ∈ chartSource j f) : chartJacobian i j e f p ≠ 0 := by
  apply right_ne_zero_of_mul_eq_one
  simpa using chartJacobian_cocycle i j i e f e p hi hj hi

def canonicalGain (i j : Index) (p : Total) : ℂ := chartJacobian j.1 i.1 j.2 i.2 p

@[simp] theorem canonicalGain_self (i : Index) (p : Total) : canonicalGain i i p = 1 := chartJacobian_self _ _ _

theorem canonicalGain_comp (i j k : Index) (p : Total)
    (hi : p ∈ chartSource i.1 i.2) (hj : p ∈ chartSource j.1 j.2) (hk : p ∈ chartSource k.1 k.2) :
    canonicalGain j k p * canonicalGain i j p = canonicalGain i k p :=
  (mul_comm _ _).trans (chartJacobian_cocycle k.1 j.1 i.1 k.2 j.2 i.2 p hk hj hi)

theorem canonicalGain_ne_zero (i j : Index) (p : Total)
    (hi : p ∈ chartSource i.1 i.2) (hj : p ∈ chartSource j.1 j.2) : canonicalGain i j p ≠ 0 :=
  chartJacobian_ne_zero j.1 i.1 j.2 i.2 p hj hi

def canonicalCore : VectorBundleCore ℂ Total ℂ Index where
  baseSet i := chartSource i.1 i.2
  isOpen_baseSet i := chartSource_isOpen i.1 i.2
  indexAt := chartIndex
  mem_baseSet_at := chartIndex_mem_source
  coordChange i j p := canonicalGain i j p • ContinuousLinearMap.id ℂ ℂ
  coordChange_self i p _ v := by simp
  continuousOn_coordChange i j := by
    have h := (chartJacobian_contMDiffOn j.1 i.1 j.2 i.2).continuousOn
    rw [Set.inter_comm] at h
    exact h.smul continuousOn_const
  coordChange_comp i j k p hp v := by
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul]
    rw [← mul_assoc,canonicalGain_comp i j k p hp.1.1 hp.1.2 hp.2]

instance canonicalCore_isContMDiff : canonicalCore.IsContMDiff 𝓘(ℂ,ChartCoord) ω where
  contMDiffOn_coordChange i j := by
    have h := chartJacobian_contMDiffOn j.1 i.1 j.2 i.2
    rw [Set.inter_comm] at h
    exact h.smul contMDiffOn_const

theorem canonicalCore_finrank (p : Total) : Module.finrank ℂ (canonicalCore.Fiber p) = 1 :=
  Module.finrank_self ℂ

theorem canonicalCore_analytic : ContMDiffVectorBundle ω ℂ canonicalCore.Fiber 𝓘(ℂ,ChartCoord) := inferInstance

/-- Restriction of the actual total-space Jacobian agrees exactly with the
already verified fibre Jacobian, in every common adapted chart. -/
theorem chartJacobian_inclusion (t : ℂ) (i j : Fin 4) (e f : Fin 2) (p : Fiber t)
    (hi : p ∈ FixedFiber.source t i e) (hj : p ∈ FixedFiber.source t j f) :
    chartJacobian i j e f (FixedFiber.inclusion t p) = FixedFiber.chartJacobian t i j e f p := by
  unfold chartJacobian FixedFiber.chartJacobian
  rw [FixedFiber.global_coordinates_eq t i e p hi]
  apply change_jacobian_eq_fiber
  have h := coordinates_mem_changeDomain i j e f (FixedFiber.inclusion t p) hi hj
  rwa [FixedFiber.global_coordinates_eq t i e p hi] at h

theorem canonicalGain_inclusion (t : ℂ) (i j : Index) (p : Fiber t)
    (hi : p ∈ FixedFiber.source t i.1 i.2) (hj : p ∈ FixedFiber.source t j.1 j.2) :
    canonicalGain i j (FixedFiber.inclusion t p) = FixedFiber.canonicalGain t i j p :=
  chartJacobian_inclusion t j.1 i.1 j.2 i.2 p hj hi

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalCanonical
