import FailureOfSemipositiveMetricExtension.FixedFiberJacobian
import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-! A genuine analytic line bundle glued from the inverse Jacobian determinants
of the actual complex surface charts.  Its scalar coordinates are the coefficients
of ordered coordinate two-forms, so the direction of the cocycle is explicit. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiber
noncomputable section
open Set Bundle Topology
open ComplexSurfaceJacobian
open scoped Manifold ContDiff

def chartJacobian (t : ℂ) (i j : Fin 4) (e f : Fin 2) (p : Fiber t) : ℂ :=
  jacobian (change t i j e f) (coordinates t i e p)

theorem coordinates_mem_changeDomain (t : ℂ) (i j : Fin 4) (e f : Fin 2) (p : Fiber t)
    (hi : p ∈ source t i e) (hj : p ∈ source t j f) :
    coordinates t i e p ∈ changeDomain t i j e f := by
  refine ⟨(chart t i e).map_source hi,?_⟩
  change param t i e (coordinates t i e p) ∈ source t j f
  rwa [param_coordinates t i e p hi]

theorem chartJacobian_contMDiffOn (t : ℂ) (i j : Fin 4) (e f : Fin 2) :
    ContMDiffOn 𝓘(ℂ,Coord) 𝓘(ℂ) ω (chartJacobian t i j e f)
      (source t i e ∩ source t j f) :=
  (change_jacobian_contDiffOn t i j e f).contMDiffOn.comp
    ((coordinates_contMDiffOn t i e ω).mono inter_subset_left)
    (fun p hp => coordinates_mem_changeDomain t i j e f p hp.1 hp.2)

theorem chartJacobian_ne_zero (t : ℂ) (i j : Fin 4) (e f : Fin 2) (p : Fiber t)
    (hi : p ∈ source t i e) (hj : p ∈ source t j f) : chartJacobian t i j e f p ≠ 0 :=
  change_jacobian_ne_zero t i j e f _ (coordinates_mem_changeDomain t i j e f p hi hj)

@[simp] theorem chartJacobian_self (t : ℂ) (i : Fin 4) (e : Fin 2) (p : Fiber t) :
    chartJacobian t i i e e p = 1 := by
  have h : change t i i e e = id := funext (coordinates_param t i e)
  simp [chartJacobian,h]

/-- The actual Jacobian determinants obey the chain-rule cocycle at every overlap point. -/
theorem chartJacobian_cocycle (t : ℂ) (i j k : Fin 4) (e f g : Fin 2) (p : Fiber t)
    (hi : p ∈ source t i e) (hj : p ∈ source t j f) (hk : p ∈ source t k g) :
    chartJacobian t j k f g p * chartJacobian t i j e f p = chartJacobian t i k e g p := by
  let q := coordinates t i e p
  have hq : q ∈ changeDomain t i j e f := coordinates_mem_changeDomain t i j e f p hi hj
  have hqk : q ∈ changeDomain t i k e g := coordinates_mem_changeDomain t i k e g p hi hk
  have hc : change t i j e f q = coordinates t j f p := by
    change coordinates t j f (param t i e (coordinates t i e p)) = _
    rw [param_coordinates t i e p hi]
  have heq : (change t j k f g ∘ change t i j e f) =ᶠ[𝓝 q] change t i k e g := by
    filter_upwards [(changeDomain_isOpen t i j e f).mem_nhds hq] with w hw
    change coordinates t k g (param t j f (coordinates t j f (param t i e w))) = _
    rw [param_coordinates t j f (param t i e w) hw.2]
    rfl
  have h := congrArg determinant (heq.fderiv_eq (𝕜 := ℂ))
  change jacobian (change t j k f g ∘ change t i j e f) q = jacobian (change t i k e g) q at h
  have hd : DifferentiableAt ℂ (change t j k f g) (change t i j e f q) := by
    rw [hc]
    exact change_differentiableAt t j k f g _ (coordinates_mem_changeDomain t j k f g p hj hk)
  rw [jacobian_comp q (change_differentiableAt t i j e f q hq) hd,hc] at h
  exact h

abbrev CanonicalIndex := Fin 4 × Fin 2

/-- Coefficients of two-forms transform by the reverse-coordinate Jacobian. -/
def canonicalGain (t : ℂ) (i j : CanonicalIndex) (p : Fiber t) : ℂ :=
  chartJacobian t j.1 i.1 j.2 i.2 p

@[simp] theorem canonicalGain_self (t : ℂ) (i : CanonicalIndex) (p : Fiber t) :
    canonicalGain t i i p = 1 := chartJacobian_self t i.1 i.2 p

theorem canonicalGain_comp (t : ℂ) (i j k : CanonicalIndex) (p : Fiber t)
    (hi : p ∈ source t i.1 i.2) (hj : p ∈ source t j.1 j.2) (hk : p ∈ source t k.1 k.2) :
    canonicalGain t j k p * canonicalGain t i j p = canonicalGain t i k p :=
  (mul_comm _ _).trans (chartJacobian_cocycle t k.1 j.1 i.1 k.2 j.2 i.2 p hk hj hi)

theorem canonicalGain_ne_zero (t : ℂ) (i j : CanonicalIndex) (p : Fiber t)
    (hi : p ∈ source t i.1 i.2) (hj : p ∈ source t j.1 j.2) : canonicalGain t i j p ≠ 0 :=
  chartJacobian_ne_zero t j.1 i.1 j.2 i.2 p hj hi

/-- An actual line-bundle core built from the Jacobians of the installed surface atlas. -/
def canonicalCore (t : ℂ) : VectorBundleCore ℂ (Fiber t) ℂ CanonicalIndex where
  baseSet i := source t i.1 i.2
  isOpen_baseSet i := source_isOpen t i.1 i.2
  indexAt := chartIndex t
  mem_baseSet_at := chartIndex_mem_source t
  coordChange i j p := canonicalGain t i j p • ContinuousLinearMap.id ℂ ℂ
  coordChange_self i p _ v := by simp [canonicalGain]
  continuousOn_coordChange i j := by
    have h := (chartJacobian_contMDiffOn t j.1 i.1 j.2 i.2).continuousOn
    rw [Set.inter_comm] at h
    exact h.smul continuousOn_const
  coordChange_comp i j k p hp v := by
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul]
    rw [← mul_assoc]
    congr 1
    exact (mul_comm _ _).trans (chartJacobian_cocycle t k.1 j.1 i.1 k.2 j.2 i.2 p hp.2 hp.1.2 hp.1.1)

instance canonicalCore_isContMDiff (t : ℂ) : (canonicalCore t).IsContMDiff 𝓘(ℂ,Coord) ω where
  contMDiffOn_coordChange i j := by
    have h := chartJacobian_contMDiffOn t j.1 i.1 j.2 i.2
    rw [Set.inter_comm] at h
    exact h.smul contMDiffOn_const

theorem canonicalCore_finrank (t : ℂ) (p : Fiber t) :
    Module.finrank ℂ ((canonicalCore t).Fiber p) = 1 := Module.finrank_self ℂ

theorem canonicalCore_analytic (t : ℂ) :
    ContMDiffVectorBundle ω ℂ (canonicalCore t).Fiber 𝓘(ℂ,Coord) := inferInstance

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiber
