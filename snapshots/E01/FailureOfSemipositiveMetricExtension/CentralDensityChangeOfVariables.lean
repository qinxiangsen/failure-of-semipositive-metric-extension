import FailureOfSemipositiveMetricExtension.MetricDensityTransition
import FailureOfSemipositiveMetricExtension.ComplexJacobianMeasure

/-! Invariance of the actual sigma norm integrals under the actual blow-up
coordinate transitions, with the real Jacobian and every frame factor checked. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set MeasureTheory
open ComplexSurfaceJacobian
open scoped ENNReal

theorem fixedFiber_change_injOn (t : ℂ) (i j : Fin 4) (e f : Fin 2) :
    InjOn (FixedFiber.change t i j e f) (FixedFiber.changeDomain t i j e f) := by
  intro q hq w hw h
  have := congrArg (FixedFiber.change t j i f e) h
  simpa only [FixedFiber.change_inverse t i j e f q hq,
    FixedFiber.change_inverse t i j e f w hw] using this

theorem sigma_density_forward_jacobian (d c : DivisionIndex) (q : FixedFiber.Coord)
    (hd : FixedFiber.param 0 d.1 d.2.1 q ∈ divisionPatch 0 d)
    (hc : FixedFiber.param 0 d.1 d.2.1 q ∈ divisionPatch 0 c) :
    ENNReal.ofReal (Complex.normSq (jacobian (FixedFiber.change 0 d.1 c.1 d.2.1 c.2.1) q)) *
      sigmaAdjointExtendedDensity c (FixedFiber.param 0 d.1 d.2.1 q) =
        sigmaAdjointExtendedDensity d (FixedFiber.param 0 d.1 d.2.1 q) := by
  let p := FixedFiber.param 0 d.1 d.2.1 q
  have hq : q ∈ FixedFiber.changeDomain 0 d.1 c.1 d.2.1 c.2.1 := by
    simpa only [p,FixedFiber.coordinates_param] using
      FixedFiber.coordinates_mem_changeDomain 0 d.1 c.1 d.2.1 c.2.1 p hd.1 hc.1
  have hi := FixedFiber.change_jacobian_inverse 0 d.1 c.1 d.2.1 c.2.1 q hq
  have hg : FixedFiber.canonicalGain 0 (divisionChart d) (divisionChart c) p =
      jacobian (FixedFiber.change 0 c.1 d.1 c.2.1 d.2.1)
        (FixedFiber.change 0 d.1 c.1 d.2.1 c.2.1 q) := rfl
  rw [sigmaAdjointExtendedDensity_transition d c _ hd hc,← mul_assoc]
  change (_ * ENNReal.ofReal (Complex.normSq (FixedFiber.canonicalGain 0 (divisionChart d) (divisionChart c) p))) * _ = _
  rw [hg,← ENNReal.ofReal_mul (Complex.normSq_nonneg _),← Complex.normSq_mul,
    mul_comm (jacobian (FixedFiber.change 0 d.1 c.1 d.2.1 c.2.1) q),hi]
  simp

theorem sigma_density_lintegral_change (d c : DivisionIndex) (S : Set FixedFiber.Coord)
    (hS : MeasurableSet S)
    (hd : MapsTo (FixedFiber.param 0 d.1 d.2.1) S (divisionPatch 0 d))
    (hc : MapsTo (FixedFiber.param 0 d.1 d.2.1) S (divisionPatch 0 c)) :
    (∫⁻ q in FixedFiber.change 0 d.1 c.1 d.2.1 c.2.1 '' S,
      sigmaAdjointExtendedDensity c (FixedFiber.param 0 c.1 c.2.1 q)) =
    ∫⁻ q in S, sigmaAdjointExtendedDensity d (FixedFiber.param 0 d.1 d.2.1 q) := by
  have hdom : S ⊆ FixedFiber.changeDomain 0 d.1 c.1 d.2.1 c.2.1 := by
    intro q hq
    simpa only [FixedFiber.coordinates_param] using
      FixedFiber.coordinates_mem_changeDomain 0 d.1 c.1 d.2.1 c.2.1
        (FixedFiber.param 0 d.1 d.2.1 q) (hd hq).1 (hc hq).1
  rw [lintegral_image_complex_jacobian hS
    (fun q hq => FixedFiber.change_differentiableAt _ _ _ _ _ q (hdom hq))
    ((fixedFiber_change_injOn _ _ _ _ _).mono hdom)]
  apply setLIntegral_congr_fun hS
  filter_upwards [] with q hq
  change _ * sigmaAdjointExtendedDensity c
    (FixedFiber.param 0 c.1 c.2.1
      (FixedFiber.coordinates 0 c.1 c.2.1 (FixedFiber.param 0 d.1 d.2.1 q))) = _
  rw [FixedFiber.param_coordinates _ _ _ _ (hc hq).1]
  exact sigma_density_forward_jacobian d c q (hd hq) (hc hq)

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
