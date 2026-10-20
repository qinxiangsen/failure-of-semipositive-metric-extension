import FailureOfSemipositiveMetricExtension.AdjointExtendedDensity

/-! Exact extended norm-density transitions, including infinite metric values.
The line-frame factors cancel and only the actual canonical Jacobian remains. -/
namespace FailureOfSemipositiveMetricExtension.Multiplier
noncomputable section
open scoped ENNReal

theorem weighted_norm_frame_change (m : ℕ) (k l f : ℂ) (hl : l ≠ 0) (w : WithBot ℝ) :
    ENNReal.ofReal (Complex.normSq ((k*l^m)*f)) *
      exponentialWeight (w + ((Real.log (Complex.normSq l) : ℝ) : WithBot ℝ)) ^ m =
    ENNReal.ofReal (Complex.normSq k) *
      (ENNReal.ofReal (Complex.normSq f) * exponentialWeight w ^ m) := by
  have hlp : 0 < Complex.normSq l := Complex.normSq_pos.mpr hl
  have hcancel : ENNReal.ofReal (Complex.normSq l) *
      ENNReal.ofReal (Real.exp (-Real.log (Complex.normSq l))) = 1 := by
    rw [← ENNReal.ofReal_mul hlp.le,Real.exp_neg,Real.exp_log hlp,mul_inv_cancel₀ hlp.ne']
    simp
  rw [Complex.normSq_mul,Complex.normSq_mul,map_pow,
    ENNReal.ofReal_mul (mul_nonneg (Complex.normSq_nonneg _) (pow_nonneg (Complex.normSq_nonneg _) _)),
    ENNReal.ofReal_mul (Complex.normSq_nonneg _),ENNReal.ofReal_pow (Complex.normSq_nonneg _),
    exponentialWeight_add]
  calc
    _ = ENNReal.ofReal (Complex.normSq k) * ENNReal.ofReal (Complex.normSq f) *
      ((ENNReal.ofReal (Complex.normSq l) * ENNReal.ofReal (Real.exp (-Real.log (Complex.normSq l))))^m *
        exponentialWeight w ^ m) := by simp only [mul_pow]; ring
    _ = _ := by rw [hcancel,one_pow,one_mul,mul_assoc]

end
end FailureOfSemipositiveMetricExtension.Multiplier

namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set
open scoped ENNReal

/-- The genuine adjoint density transforms by the squared norm of the reverse
coordinate Jacobian, exactly as a canonical-volume density must. -/
theorem sigmaAdjointExtendedDensity_transition (d c : DivisionIndex) (p : Fiber 0)
    (hd : p ∈ divisionPatch 0 d) (hc : p ∈ divisionPatch 0 c) :
    sigmaAdjointExtendedDensity c p =
      ENNReal.ofReal (Complex.normSq (FixedFiber.canonicalGain 0 (divisionChart d) (divisionChart c) p)) *
        sigmaAdjointExtendedDensity d p := by
  unfold sigmaAdjointExtendedDensity
  rw [← sigmaAdjointCoefficient_compatible d c p hd hc,
    centralH0.compatible (divisionFrame d) (divisionFrame c) p ⟨hd.2,hc.2⟩]
  exact FailureOfSemipositiveMetricExtension.Multiplier.weighted_norm_frame_change 4 _ _ _
    (gain_ne_zero 0 (-2) (fun _ => 1) (divisionFrame d) (divisionFrame c) p ⟨hd.2,hc.2⟩) _

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
