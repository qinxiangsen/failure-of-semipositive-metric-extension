import FailureOfSemipositiveMetricExtension.MetricRelativePotential
import FailureOfSemipositiveMetricExtension.MetricPlurisubharmonicity

/-! The final compactness step of minimal singularities on the actual surface.
Residual existence is an EXPLICIT UNPROVED HYPOTHESIS of the conditional theorem,
not an axiom or a claimed proof of Siu/Zariski applicability. -/
namespace FailureOfSemipositiveMetricExtension
noncomputable section

theorem withBot_le_of_double_le (u v : WithBot ℝ) (C : ℝ)
    (h : u+u ≤ v+v+(C : WithBot ℝ)) : u ≤ v+((C/2 : ℝ) : WithBot ℝ) := by
  cases u with
  | bot => exact bot_le
  | coe a =>
    cases v with
    | bot => simp at h
    | coe b =>
      simp only [← WithBot.coe_add,WithBot.coe_le_coe] at h ⊢
      linarith

end
end FailureOfSemipositiveMetricExtension

namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set

/-- Actual compatible residual A-weights after removing one copy of ell from
2h. The existence of this object is the Siu/Zariski step still to be proved. -/
structure HalfDivisorResidual (h : SingularHermitianWeight 0 (-2) (fun _ => 1)) where
  remainder : SingularHermitianWeight 0 (-2) centralADegree
  upperSemicontinuous : ∀ i, UpperSemicontinuousOn (remainder.weight i) (baseSet 0 i)
  square_identity : ∀ i p, p ∈ baseSet 0 i →
    h.weight i p + h.weight i p = remainder.weight i p + (divisorWeight ellSection).weight i p

/-- Once the genuine residual exists, the compact relative-potential argument
proves the required global singularity comparison in ALL actual frames. -/
theorem central_weight_le_h0_of_residual
    (h : SingularHermitianWeight 0 (-2) (fun _ => 1)) (r : HalfDivisorResidual h) :
    ∃ C : ℝ, ∀ i p, p ∈ baseSet 0 i →
      h.weight i p ≤ centralH0.weight i p + (C : WithBot ℝ) := by
  obtain ⟨C,hC⟩ := weight_le_smooth_add_const r.remainder centralAMetric r.upperSemicontinuous
  refine ⟨C/2,?_⟩
  intro i p hp
  apply FailureOfSemipositiveMetricExtension.withBot_le_of_double_le
  rw [r.square_identity i p hp,centralH0_square]
  calc
    r.remainder.weight i p + (divisorWeight ellSection).weight i p ≤
        ((smoothMetricWeight centralAMetric).weight i p + (C : WithBot ℝ)) +
          (divisorWeight ellSection).weight i p := add_le_add_right (hC i p hp) _
    _ = (smoothMetricWeight centralAMetric).weight i p +
        (divisorWeight ellSection).weight i p + (C : WithBot ℝ) := by rw [add_right_comm]

/-- Standard comparison definition in terms of the actual compatible psh
weights. Including identically −∞ weights does not weaken the condition. -/
def HasMinimalSingularities {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ}
    (h : SingularHermitianWeight t a b) : Prop :=
  HasPlurisubharmonicWeights h ∧
    ∀ g : SingularHermitianWeight t a b, HasPlurisubharmonicWeights g →
      ∃ C : ℝ, ∀ i p, p ∈ baseSet t i → g.weight i p ≤ h.weight i p + (C : WithBot ℝ)

/-- Conditional final step only. The quantified residual-existence premise is
not discharged in this module and is not introduced as a literature axiom. -/
theorem centralH0_minimal_of_residual_decompositions
    (H : ∀ h : SingularHermitianWeight 0 (-2) (fun _ => 1), HasPlurisubharmonicWeights h →
      Nonempty (HalfDivisorResidual h)) : HasMinimalSingularities centralH0 := by
  refine ⟨centralH0_plurisubharmonic,?_⟩
  intro h hh
  obtain ⟨r⟩ := H h hh
  exact central_weight_le_h0_of_residual h r

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
