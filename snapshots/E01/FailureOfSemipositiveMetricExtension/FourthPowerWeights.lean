import FailureOfSemipositiveMetricExtension.PlurisubharmonicScaling
import FailureOfSemipositiveMetricExtension.FourthPowerLineBundle
import FailureOfSemipositiveMetricExtension.CentralRestrictionWellDefined

/-! Exact fourth-power normalization for the generic Cao input: the true line
cocycle is g^4, its weight is 4φ, and its m=1 integrable germs are exactly those
computed with φ and m=4. Psh scaling is proved, not externally assumed. -/
namespace FailureOfSemipositiveMetricExtension
noncomputable section
open Set MeasureTheory
open scoped ENNReal

theorem scaleWeight_add_real (c a : ℝ) (u : WithBot ℝ) :
    scaleWeight c (u + (a : WithBot ℝ)) = scaleWeight c u + ((c*a : ℝ) : WithBot ℝ) := by
  cases u with
  | bot => simp
  | coe x => simp only [← WithBot.coe_add,scaleWeight_coe]; congr 1; ring

@[simp] theorem scaleWeight_eq_bot_iff (c : ℝ) (u : WithBot ℝ) :
    scaleWeight c u = ⊥ ↔ u = ⊥ := by
  cases u with
  | bot => rfl
  | coe x =>
    change ((c*x : ℝ) : WithBot ℝ) = ⊥ ↔ (x : WithBot ℝ) = ⊥
    simp only [WithBot.coe_ne_bot]

theorem exponentialWeight_scale_four (u : WithBot ℝ) :
    Multiplier.exponentialWeight (scaleWeight 4 u) = Multiplier.exponentialWeight u ^ 4 := by
  cases u with
  | bot => simp
  | coe x =>
    rw [scaleWeight_coe,Multiplier.exponentialWeight_coe,Multiplier.exponentialWeight_coe,
      ← ENNReal.ofReal_pow (Real.exp_pos _).le,← Real.exp_nat_mul]
    congr 2
    ring

theorem PlurisubharmonicOn.mono_domain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u : E → WithBot ℝ} {U V : Set E} (hu : PlurisubharmonicOn u U) (hV : V ⊆ U) :
    PlurisubharmonicOn u V :=
  ⟨hu.1.mono hV,fun x v r hr hd N => hu.2 x v r hr (fun z hz => hV (hd z hz)) N⟩

theorem integrableGerm_scale_four_iff (M : Type) [TopologicalSpace M]
    [ChartedSpace Multiplier.Coord M] (w : M → WithBot ℝ) (p : M) (g : Multiplier.Stalk M p) :
    Multiplier.IntegrableGerm M 1 (fun q => scaleWeight 4 (w q)) p g ↔
      Multiplier.IntegrableGerm M 4 w p g := by
  simp only [Multiplier.IntegrableGerm,exponentialWeight_scale_four,pow_one]

end
end FailureOfSemipositiveMetricExtension

namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.CaoAdapter
noncomputable section
open Set TopologicalSpace
open scoped Manifold ContDiff

/-- The actual candidate metric on the genuine fourth tensor-power bundle. -/
def fourthPowerWeight {U : Opens Total}
    (h : GlobalLineBundle.SingularWeightOn U (-2) (fun _ => 1))
    (hpsh : h.HasPlurisubharmonicWeights) :
    CaoExtensionInterface.SemipositiveWeightOn family fourthPowerLine U where
  weight d p := scaleWeight 4 (h.weight (GlobalLineBundle.divisionFrame d) p)
  compatible d c p hp hd := by
    rw [h.compatible (GlobalLineBundle.divisionFrame d) (GlobalLineBundle.divisionFrame c) p hp ⟨hd.1.2,hd.2.2⟩,
      scaleWeight_add_real]
    change _ = _ + ((Real.log (Complex.normSq (powerGain d c p)) : ℝ) : WithBot ℝ)
    rw [powerGain,map_pow,Real.log_pow]
    norm_num
  psh a d := by
    have hu := (hpsh (GlobalLineBundle.divisionFrame d) a.1 a.2).scale_ge_one
      (GlobalLineBundle.globalWeightChartDomain_isOpen U (GlobalLineBundle.divisionFrame d) a.1 a.2)
      4 (by norm_num)
    apply hu.mono_domain
    intro q hq
    exact ⟨hq.1,hq.2.1.2,hq.2.2⟩

theorem fourthPowerWeight_wellDefined {U : Opens Total}
    (h : GlobalLineBundle.SingularWeightOn U (-2) (fun _ => 1))
    (hpsh : h.HasPlurisubharmonicWeights) (hc : h.centralDominatesH0) :
    CaoExtensionInterface.RestrictionWellDefined family fourthPowerLine (fourthPowerWeight h hpsh) := by
  intro p
  obtain ⟨q,hq,hnell⟩ := FixedFiberBundle.ell_nonzero_in_every_component p
  obtain ⟨d,hd⟩ := GlobalLineBundle.divisionPatch_cover (FixedFiber.inclusion 0 q)
  refine ⟨q,hq,d,hd,?_⟩
  change scaleWeight 4 (h.weight (GlobalLineBundle.divisionFrame d) (FixedFiber.inclusion 0 q)) ≠ ⊥
  rw [ne_eq,scaleWeight_eq_bot_iff]
  obtain ⟨C,hC⟩ := hc
  have hz := hC (GlobalLineBundle.divisionFrame d) q hd.2
  intro hb
  rw [hb] at hz
  have := le_bot_iff.mp hz
  simpa [FixedFiberBundle.centralH0_ne_bot_off_ell _ _ hd.2 hnell] using this

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.CaoAdapter
