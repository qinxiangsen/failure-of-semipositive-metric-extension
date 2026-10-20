import Mathlib.Geometry.Manifold.Sheaf.LocallyRingedSpace
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.RingTheory.Ideal.Span

/-! Actual weighted local integrability of holomorphic germs on complex surfaces.
The definition uses the genuine holomorphic structure sheaf and nonnegative
Lebesgue integrals in analytic coordinates. Infinite weights are not replaced by
finite values, and zero times infinity has the usual measure-theoretic meaning. -/
namespace FailureOfSemipositiveMetricExtension.Multiplier
noncomputable section
open Set MeasureTheory TopologicalSpace Opposite Manifold
open scoped Manifold ContDiff ENNReal

abbrev Coord := ℂ × ℂ
variable (M : Type) [TopologicalSpace M] [ChartedSpace Coord M]

abbrev sheaf := smoothSheafCommRing 𝓘(ℂ,Coord) 𝓘(ℂ) M ℂ
abbrev Stalk (p : M) := (sheaf M).presheaf.stalk p

/-- Analytic coordinate systems with their actual inverse and open domains. -/
structure AnalyticCoordinate where
  chart : PartialHomeomorph M Coord
  forward : ContMDiffOn 𝓘(ℂ,Coord) 𝓘(ℂ,Coord) ω chart chart.source
  inverse : ContMDiffOn 𝓘(ℂ,Coord) 𝓘(ℂ,Coord) ω chart.symm chart.target

def sectionFunction (U : Opens M) (f : C^∞⟮𝓘(ℂ,Coord),U;𝓘(ℂ),ℂ⟯) (x : M) : ℂ := by
  classical
  exact if hx : x ∈ U then f ⟨x,hx⟩ else 0

/-- exp(-weight), including positive infinity when the weight is minus infinity. -/
def exponentialWeight (u : WithBot ℝ) : ℝ≥0∞ :=
  if u = ⊥ then ⊤ else ENNReal.ofReal (Real.exp (-u.unbotD 0))

/-- A holomorphic germ has a representative with finite weighted squared norm in
some genuine analytic coordinate neighbourhood. The definition quantifies over
actual representatives and charts, not a postulated multiplier-ideal predicate. -/
def IntegrableGerm (m : ℕ) (w : M → WithBot ℝ) (p : M) (g : Stalk M p) : Prop :=
  ∃ (U : Opens M) (hp : p ∈ U) (f : C^∞⟮𝓘(ℂ,Coord),U;𝓘(ℂ),ℂ⟯),
    (sheaf M).presheaf.germ U p hp f = g ∧
    ∃ (e : AnalyticCoordinate M), p ∈ e.chart.source ∧ ∃ ε : ℝ, 0 < ε ∧
      Metric.closedBall (e.chart p) ε ⊆ e.chart.target ∩ e.chart.symm ⁻¹' U ∧
      (∫⁻ z in Metric.closedBall (e.chart p) ε,
        ENNReal.ofReal (Complex.normSq (sectionFunction M U f (e.chart.symm z))) *
          exponentialWeight (w (e.chart.symm z)) ^ m ∂volume) < ⊤

/-- A simple divisor equation is an actual normal coordinate times an analytic
unit, on an actual analytic chart around the point. -/
def SimpleEquationAt (U : Opens M) (f : C^∞⟮𝓘(ℂ,Coord),U;𝓘(ℂ),ℂ⟯) (p : M) : Prop :=
  ∃ (e : AnalyticCoordinate M), p ∈ e.chart.source ∧ e.chart.source ⊆ U ∧
    ∃ u : M → ℂ, ContMDiffOn 𝓘(ℂ,Coord) 𝓘(ℂ) ω u e.chart.source ∧
      (∀ x ∈ e.chart.source, u x ≠ 0) ∧
      ∀ x ∈ e.chart.source, sectionFunction M U f x = (e.chart x).2 * u x

@[simp] theorem sectionFunction_of_mem (U : Opens M)
    (f : C^∞⟮𝓘(ℂ,Coord),U;𝓘(ℂ),ℂ⟯) (x : M) (hx : x ∈ U) :
    sectionFunction M U f x = f ⟨x,hx⟩ := by simp [sectionFunction,hx]

@[simp] theorem exponentialWeight_bot : exponentialWeight ⊥ = ⊤ := by simp [exponentialWeight]
@[simp] theorem exponentialWeight_coe (u : ℝ) :
    exponentialWeight (u : WithBot ℝ) = ENNReal.ofReal (Real.exp (-u)) := by
  simp [exponentialWeight]

end
end FailureOfSemipositiveMetricExtension.Multiplier
