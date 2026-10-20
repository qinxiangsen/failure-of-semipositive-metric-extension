import Mathlib.Topology.Semicontinuous
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Data.Complex.Basic

/-! Plurisubharmonicity defined by upper semicontinuity and the actual circular
submean inequalities on complex affine discs. Minus-infinity values are handled
by all lower truncations, so no undefined extended-real Bochner integral occurs.
This is the decreasing-truncation formulation of the usual extended integral. -/
namespace FailureOfSemipositiveMetricExtension
noncomputable section
open Set MeasureTheory

/-- The finite lower truncation max(u,-N), also at u=-infinity. -/
def lowerTruncation (N : ℕ) (u : WithBot ℝ) : ℝ := max (u.unbotD (-(N:ℝ))) (-(N:ℝ))

def complexCircle (r θ : ℝ) : ℂ := (r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I)

/-- Genuine submean definition on a normed complex space; only discs contained
in the specified set are tested. The intended domains are open. -/
def PlurisubharmonicOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u : E → WithBot ℝ) (U : Set E) : Prop :=
  UpperSemicontinuousOn u U ∧
    ∀ (x v : E) (r : ℝ), 0 < r →
      (∀ z : ℂ, ‖z‖ ≤ r → x + z • v ∈ U) → ∀ N : ℕ,
      u x ≤ (((2*Real.pi)⁻¹ *
        ∫ θ in (0:ℝ)..(2*Real.pi), lowerTruncation N (u (x + complexCircle r θ • v)) : ℝ) : WithBot ℝ)

def logSumSquaresWeight {E : Type*} {m : ℕ} (c : ℝ) (f : Fin m → E → ℂ) (x : E) : WithBot ℝ :=
  if (∑ k, Complex.normSq (f k x)) = 0 then ⊥ else
    ((c * Real.log (∑ k, Complex.normSq (f k x)) : ℝ) : WithBot ℝ)

theorem norm_complexCircle (r θ : ℝ) (hr : 0 ≤ r) : ‖complexCircle r θ‖ = r := by
  simp [complexCircle,norm_mul,Complex.norm_exp,abs_of_nonneg hr]

theorem PlurisubharmonicOn.congrOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u v : E → WithBot ℝ} {U : Set E} (h : PlurisubharmonicOn u U)
    (heq : EqOn u v U) : PlurisubharmonicOn v U := by
  constructor
  · intro x hx y hy
    rw [← heq hx] at hy
    filter_upwards [h.1 x hx y hy,self_mem_nhdsWithin] with z hz hzU
    rwa [← heq hzU]
  · intro x w r hr hd N
    have hx : x ∈ U := by simpa using hd 0 (by simpa using hr.le)
    have hcircle : ∀ θ, x + complexCircle r θ • w ∈ U :=
      fun θ => hd _ (le_of_eq (norm_complexCircle r θ hr.le))
    have hf : (fun θ => lowerTruncation N (u (x + complexCircle r θ • w))) =
        (fun θ => lowerTruncation N (v (x + complexCircle r θ • w))) := by
      funext θ
      rw [heq (hcircle θ)]
    rw [← heq hx,← hf]
    exact h.2 x w r hr hd N

theorem PlurisubharmonicOn.congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u v : E → WithBot ℝ} {U : Set E} (h : PlurisubharmonicOn u U)
    (heq : ∀ x, u x = v x) : PlurisubharmonicOn v U := by
  have : u = v := funext heq
  rwa [← this]

end
end FailureOfSemipositiveMetricExtension
