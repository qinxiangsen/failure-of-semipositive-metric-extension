import FailureOfSemipositiveMetricExtension.CentralSingularWeight
import FailureOfSemipositiveMetricExtension.CentralAuxiliaryZeroSets

/-! Smooth regular parts and exact logarithmic normal forms for the actual
prescribed singular weights. No psh or Lelong-number axiom is introduced. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold
open scoped Manifold ContDiff

/-- Smooth regular part in a genuine frame and genuine normal coordinate. -/
def centralH0RegularPart (d : DivisionIndex) (p : Fiber 0) : ℝ :=
  (Real.log (sectionNormSum liftedCentralCubics (divisionFrame d) p) +
    Real.log (Complex.normSq (ellLocalUnit d p))) / 2

theorem centralH0RegularPart_contMDiffOn (d : DivisionIndex) :
    ContMDiffOn 𝓘(ℝ,FixedFiber.Coord) 𝓘(ℝ) ω (centralH0RegularPart d) (divisionPatch 0 d) := by
  have hS := (sectionNormSum_contMDiffOn liftedCentralCubics (divisionFrame d)).mono
    (divisionPatch_subset_frame 0 d)
  have hLS := Real.contDiffOn_log.contMDiffOn.comp hS (fun p hp => by
    simpa using ne_of_gt (sectionNormSum_positive liftedCentralCubics
      liftedCentralCubics_basepoint_free (divisionFrame d) p hp.2))
  have hU := (FailureOfSemipositiveMetricExtension.normSq_contDiff_real ω).contMDiff.comp_contMDiffOn
    (FailureOfSemipositiveMetricExtension.complex_contMDiffOn_real (ellLocalUnit_contMDiffOn d))
  have hLU := Real.contDiffOn_log.contMDiffOn.comp hU (fun p hp => by
    simpa using ne_of_gt (Complex.normSq_pos.mpr (ellLocalUnit_ne_zero d p hp)))
  have hC : ContMDiffOn 𝓘(ℝ,FixedFiber.Coord) 𝓘(ℝ) ω (fun _ : Fiber 0 => (2 : ℝ)⁻¹) (divisionPatch 0 d) := contMDiffOn_const
  simpa only [centralH0RegularPart,div_eq_mul_inv,smul_eq_mul] using (hLS.add hLU).smul hC

theorem centralH0_logarithmic_normal_form (d : DivisionIndex) (hr : d.1 ≠ 3)
    (he : d.2.1 = 0) (p : Fiber 0) (hp : p ∈ divisionPatch 0 d) :
    centralH0.weight (divisionFrame d) p =
      if (FixedFiber.coordinates 0 d.1 d.2.1 p).2 = 0 then ⊥ else
        ((centralH0RegularPart d p +
          Real.log (Complex.normSq (FixedFiber.coordinates 0 d.1 d.2.1 p).2) / 2 : ℝ) : WithBot ℝ) := by
  have hc := ellSection_coefficient_simple d hr he p hp
  have hu := ellLocalUnit_ne_zero d p hp
  by_cases hs : (FixedFiber.coordinates 0 d.1 d.2.1 p).2 = 0
  · have hz : ellSection.coefficient (divisionFrame d) p = 0 := by rw [hc,hs,zero_mul]
    simp [centralH0,hs,hz]
  · have hn : ellSection.coefficient (divisionFrame d) p ≠ 0 := by rw [hc]; exact mul_ne_zero hs hu
    simp only [centralH0,hs,hn,if_false]
    apply congrArg (fun x : ℝ => (x : WithBot ℝ))
    unfold centralH0RealWeight centralH0RegularPart
    rw [hc,Complex.normSq_mul,Real.log_mul (ne_of_gt (Complex.normSq_pos.mpr hs))
      (ne_of_gt (Complex.normSq_pos.mpr hu))]
    ring

/-- Every singular point admits the exact coefficient-one-half normal form,
with a proved real-analytic remainder on an actual open bundle/chart patch. -/
theorem centralH0_local_normal_form (p : Fiber 0) (hz : sectionValue ellSection p = 0) :
    ∃ d : DivisionIndex, p ∈ divisionPatch 0 d ∧
      ContMDiffOn 𝓘(ℝ,FixedFiber.Coord) 𝓘(ℝ) ω (centralH0RegularPart d) (divisionPatch 0 d) ∧
      ∀ q ∈ divisionPatch 0 d, centralH0.weight (divisionFrame d) q =
        if (FixedFiber.coordinates 0 d.1 d.2.1 q).2 = 0 then ⊥ else
          ((centralH0RegularPart d q +
            Real.log (Complex.normSq (FixedFiber.coordinates 0 d.1 d.2.1 q).2) / 2 : ℝ) : WithBot ℝ) := by
  obtain ⟨d,hp,hr,he,_⟩ := ellSection_simple_at_zero p hz
  exact ⟨d,hp,centralH0RegularPart_contMDiffOn d,
    fun q hq => centralH0_logarithmic_normal_form d hr he q hq⟩

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
