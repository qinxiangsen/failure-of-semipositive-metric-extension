import FailureOfSemipositiveMetricExtension.CentralSimpleDivisor
import FailureOfSemipositiveMetricExtension.CentralSingularWeight
import FailureOfSemipositiveMetricExtension.Literature.MultiplierSmoothDivisor

/-! The actual multiplier-integrability germs of h0, in every bundle frame,
identified with the actual ell-power ideals. The only external input here is the
generic smooth-divisor multiplier theorem; all its concrete hypotheses are proved. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold TopologicalSpace
open scoped Manifold ContDiff

def centralH0SmoothPart (i : Index) (p : Fiber 0) : ℝ :=
  Real.log (sectionNormSum liftedCentralCubics i p) / 2

theorem centralH0SmoothPart_contMDiffOn (i : Index) :
    ContMDiffOn 𝓘(ℝ,FixedFiber.Coord) 𝓘(ℝ) ω (centralH0SmoothPart i) (baseSet 0 i) := by
  have hL := Real.contDiffOn_log.contMDiffOn.comp (sectionNormSum_contMDiffOn liftedCentralCubics i)
    (fun p hp => by simpa using ne_of_gt (sectionNormSum_positive liftedCentralCubics
      liftedCentralCubics_basepoint_free i p hp))
  have hC : ContMDiffOn 𝓘(ℝ,FixedFiber.Coord) 𝓘(ℝ) ω (fun _ : Fiber 0 => (2:ℝ)⁻¹) (baseSet 0 i) := contMDiffOn_const
  simpa only [centralH0SmoothPart,div_eq_mul_inv,smul_eq_mul] using hL.smul hC

theorem centralH0_smooth_divisor_formula (i : Index) (p : Fiber 0) (hp : p ∈ baseSet 0 i) :
    centralH0.weight i p =
      if FailureOfSemipositiveMetricExtension.Multiplier.sectionFunction (Fiber 0) (frameOpen 0 i)
        (coefficientSection ellSection i) p = 0 then ⊥ else
      ((centralH0SmoothPart i p + (1/2:ℝ) * Real.log (Complex.normSq
        (FailureOfSemipositiveMetricExtension.Multiplier.sectionFunction (Fiber 0) (frameOpen 0 i)
          (coefficientSection ellSection i) p)) : ℝ) : WithBot ℝ) := by
  rw [FailureOfSemipositiveMetricExtension.Multiplier.sectionFunction_of_mem _ _ _ p hp]
  change (if ellSection.coefficient i p = 0 then ⊥ else (centralH0RealWeight i p : WithBot ℝ)) = _
  change _ = if ellSection.coefficient i p = 0 then ⊥ else
    ((centralH0SmoothPart i p + (1/2:ℝ) * Real.log (Complex.normSq (ellSection.coefficient i p)) : ℝ) : WithBot ℝ)
  split_ifs
  · rfl
  · congr 1
    unfold centralH0SmoothPart centralH0RealWeight
    ring

/-- Every actual frame has the same genuine multiplier-integrability germs.
The exponent is natural-number division m/2, including m=0. -/
theorem centralH0_multiplierGerm_iff (m : ℕ) (i : Index) (p : Fiber 0)
    (hp : p ∈ baseSet 0 i) (g : HolomorphicStalk 0 p) :
    FailureOfSemipositiveMetricExtension.Multiplier.IntegrableGerm (Fiber 0) m (centralH0.weight i) p g ↔
      g ∈ ellPowerStalkIdeal (m/2) p := by
  have h := FailureOfSemipositiveMetricExtension.Literature.smooth_divisor_multiplier_germ (Fiber 0)
    (frameOpen 0 i) (coefficientSection ellSection i) p hp
    (centralH0SmoothPart i) (centralH0SmoothPart_contMDiffOn i).continuousOn
    (1/2) (by norm_num) (centralH0.weight i)
    (fun q hq => centralH0_smooth_divisor_formula i q hq)
    (ellSection_simple_equation i p hp) m g
  have he : Nat.floor ((m:ℝ)*(1/2)) = m/2 := by
    rw [show (m:ℝ)*(1/2) = (m:ℝ)/2 by ring]
    simp [Nat.floor_div_ofNat]
  rw [he] at h
  rw [ellPowerStalkIdeal,divisorPowerStalkIdeal_eq_frame ellSection (m/2) i p hp]
  exact h

theorem centralH0_multiplier_frame_independent (m : ℕ) (i j : Index) (p : Fiber 0)
    (hi : p ∈ baseSet 0 i) (hj : p ∈ baseSet 0 j) (g : HolomorphicStalk 0 p) :
    FailureOfSemipositiveMetricExtension.Multiplier.IntegrableGerm (Fiber 0) m (centralH0.weight i) p g ↔
      FailureOfSemipositiveMetricExtension.Multiplier.IntegrableGerm (Fiber 0) m (centralH0.weight j) p g := by
  rw [centralH0_multiplierGerm_iff m i p hi,centralH0_multiplierGerm_iff m j p hj]

/-- The integrability-first carrier, allowing any actual local frame. -/
def centralMultiplierStalkSet (m : ℕ) (p : Fiber 0) : Set (HolomorphicStalk 0 p) :=
  {g | ∃ i : Index, p ∈ baseSet 0 i ∧
    FailureOfSemipositiveMetricExtension.Multiplier.IntegrableGerm (Fiber 0) m (centralH0.weight i) p g}

theorem centralMultiplierStalkSet_eq (m : ℕ) (p : Fiber 0) :
    centralMultiplierStalkSet m p = (ellPowerStalkIdeal (m/2) p : Set (HolomorphicStalk 0 p)) := by
  ext g
  constructor
  · rintro ⟨i,hi,hg⟩
    exact (centralH0_multiplierGerm_iff m i p hi g).mp hg
  · intro hg
    let i := (core 0 (-2) (fun _ => 1)).indexAt p
    have hi : p ∈ baseSet 0 i := (core 0 (-2) (fun _ => 1)).mem_baseSet_at p
    exact ⟨i,hi,(centralH0_multiplierGerm_iff m i p hi g).mpr hg⟩

/-- An actual ideal whose carrier is defined by weighted local integrability. -/
def centralMultiplierStalkIdeal (m : ℕ) (p : Fiber 0) : Ideal (HolomorphicStalk 0 p) where
  carrier := centralMultiplierStalkSet m p
  zero_mem' := by rw [centralMultiplierStalkSet_eq]; exact (ellPowerStalkIdeal (m/2) p).zero_mem
  add_mem' := by
    intro f g hf hg
    rw [centralMultiplierStalkSet_eq] at hf hg ⊢
    exact (ellPowerStalkIdeal (m/2) p).add_mem hf hg
  smul_mem' := by
    intro f g hg
    rw [centralMultiplierStalkSet_eq] at hg ⊢
    exact (ellPowerStalkIdeal (m/2) p).smul_mem f hg

theorem centralMultiplierStalkIdeal_eq (m : ℕ) (p : Fiber 0) :
    centralMultiplierStalkIdeal m p = ellPowerStalkIdeal (m/2) p := by
  apply SetLike.coe_injective
  exact centralMultiplierStalkSet_eq m p

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
