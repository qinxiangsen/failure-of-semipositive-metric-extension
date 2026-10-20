import FailureOfSemipositiveMetricExtension.MultiplierGerms
import FailureOfSemipositiveMetricExtension.FourthPowerWeights

/-! Genuine holomorphic weighted-integrability germs in every finite complex
dimension. This is the full-dimensional analogue of the actual surface germs. -/
namespace FailureOfSemipositiveMetricExtension.GeneralMultiplier
noncomputable section
open Set MeasureTheory TopologicalSpace Opposite Manifold
open scoped Manifold ContDiff ENNReal

abbrev Coord (n : ℕ) := Fin n → ℂ
variable (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (Coord n) M]

abbrev sheaf := smoothSheafCommRing 𝓘(ℂ,Coord n) 𝓘(ℂ) M ℂ
abbrev Stalk (p : M) := (sheaf n M).presheaf.stalk p

structure AnalyticCoordinate where
  chart : PartialHomeomorph M (Coord n)
  forward : ContMDiffOn 𝓘(ℂ,Coord n) 𝓘(ℂ,Coord n) ω chart chart.source
  inverse : ContMDiffOn 𝓘(ℂ,Coord n) 𝓘(ℂ,Coord n) ω chart.symm chart.target

def sectionFunction (U : Opens M) (f : C^∞⟮𝓘(ℂ,Coord n),U;𝓘(ℂ),ℂ⟯) (x : M) : ℂ := by
  classical
  exact if hx : x ∈ U then f ⟨x,hx⟩ else 0

def IntegrableGerm (m : ℕ) (w : M → WithBot ℝ) (p : M) (g : Stalk n M p) : Prop :=
  ∃ (U : Opens M) (hp : p ∈ U) (f : C^∞⟮𝓘(ℂ,Coord n),U;𝓘(ℂ),ℂ⟯),
    (sheaf n M).presheaf.germ U p hp f = g ∧
    ∃ (e : AnalyticCoordinate n M), p ∈ e.chart.source ∧ ∃ ε : ℝ, 0 < ε ∧
      Metric.closedBall (e.chart p) ε ⊆ e.chart.target ∩ e.chart.symm ⁻¹' U ∧
      (∫⁻ z in Metric.closedBall (e.chart p) ε,
        ENNReal.ofReal (Complex.normSq (sectionFunction n M U f (e.chart.symm z))) *
          Multiplier.exponentialWeight (w (e.chart.symm z)) ^ m ∂volume) < ⊤

@[simp] theorem sectionFunction_of_mem (U : Opens M)
    (f : C^∞⟮𝓘(ℂ,Coord n),U;𝓘(ℂ),ℂ⟯) (x : M) (hx : x ∈ U) :
    sectionFunction n M U f x = f ⟨x,hx⟩ := by simp [sectionFunction,hx]

theorem exponentialWeight_scale_nat (m : ℕ) (hm : 0 < m) (u : WithBot ℝ) :
    Multiplier.exponentialWeight (scaleWeight (m : ℝ) u) = Multiplier.exponentialWeight u ^ m := by
  cases u with
  | bot => simp [hm.ne']
  | coe x =>
    rw [scaleWeight_coe,Multiplier.exponentialWeight_coe,Multiplier.exponentialWeight_coe,
      ← ENNReal.ofReal_pow (Real.exp_pos _).le,← Real.exp_nat_mul]
    congr 2
    ring

theorem integrableGerm_scale_nat_iff (m : ℕ) (hm : 0 < m)
    (w : M → WithBot ℝ) (p : M) (g : Stalk n M p) :
    IntegrableGerm n M 1 (fun q => scaleWeight (m : ℝ) (w q)) p g ↔
      IntegrableGerm n M m w p g := by
  simp only [IntegrableGerm,exponentialWeight_scale_nat m hm,pow_one]

end
end FailureOfSemipositiveMetricExtension.GeneralMultiplier
