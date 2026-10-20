import FailureOfSemipositiveMetricExtension.GlobalHomogeneousSections
import FailureOfSemipositiveMetricExtension.Cubics

/-!
The four cubic polynomials give actual complex-analytic sections of the pullback
of O(3) on the global blow-up family. Their values are independent of the family
parameter. No exceptional divisor has yet been divided out.
-/
namespace FailureOfSemipositiveMetricExtension.GlobalLineBundle
noncomputable section
open Set Bundle IsManifold FailureOfSemipositiveMetricExtension.GlobalIncidence
open scoped Manifold ContDiff

/-- The paper's four ordered, parameter-independent homogeneous cubic generators. -/
def cubicGenerators (k : Fin 4) : HomogeneousData 3 where
  value q := ![FailureOfSemipositiveMetricExtension.Cubics.g₁ (q.2 0) (q.2 1) (q.2 2),
    FailureOfSemipositiveMetricExtension.Cubics.g₂ (q.2 0) (q.2 1) (q.2 2),
    FailureOfSemipositiveMetricExtension.Cubics.g₃ (q.2 0) (q.2 1) (q.2 2),
    FailureOfSemipositiveMetricExtension.Cubics.g₄ (q.2 0) (q.2 1) (q.2 2)] k
  analytic := by
    fin_cases k <;>
      dsimp [FailureOfSemipositiveMetricExtension.Cubics.g₁,FailureOfSemipositiveMetricExtension.Cubics.g₂,
        FailureOfSemipositiveMetricExtension.Cubics.g₃,FailureOfSemipositiveMetricExtension.Cubics.g₄] <;> fun_prop
  homogeneous t c v := by
    fin_cases k <;>
      simp [FailureOfSemipositiveMetricExtension.Cubics.g₁,FailureOfSemipositiveMetricExtension.Cubics.g₂,
        FailureOfSemipositiveMetricExtension.Cubics.g₃,FailureOfSemipositiveMetricExtension.Cubics.g₄,
        Pi.smul_apply,smul_eq_mul,zpow_ofNat] <;> ring

/-- Exact identification with the coefficient-level cubic generators. -/
theorem cubicGenerators_value (k : Fin 4) (t : ℂ) (v : Fin 3 → ℂ) :
    (cubicGenerators k).value (t,v) =
      ![FailureOfSemipositiveMetricExtension.Cubics.g₁ (v 0) (v 1) (v 2),
        FailureOfSemipositiveMetricExtension.Cubics.g₂ (v 0) (v 1) (v 2),
        FailureOfSemipositiveMetricExtension.Cubics.g₃ (v 0) (v 1) (v 2),
        FailureOfSemipositiveMetricExtension.Cubics.g₄ (v 0) (v 1) (v 2)] k := rfl

theorem cubicGenerators_parameter_independent (k : Fin 4) (t u : ℂ) (v : Fin 3 → ℂ) :
    (cubicGenerators k).value (t,v) = (cubicGenerators k).value (u,v) := rfl

/-- Genuine sections of the global degree-three line bundle, before exceptional division. -/
def cubicSections (k : Fin 4) : SectionData 3 (fun _ => 0) :=
  homogeneousSection (cubicGenerators k)

/-- The section maps into the actual total space are complex analytic. -/
theorem cubicSections_analytic (k : Fin 4) :
    ContMDiff 𝓘(ℂ,ChartCoord) (𝓘(ℂ,ChartCoord).prod 𝓘(ℂ)) ω
      (sectionMap (cubicSections k)) := sectionMap_contMDiff _

@[simp] theorem cubicSections_projects (k : Fin 4) (p : Total) :
    (core 3 (fun _ => 0)).proj (sectionMap (cubicSections k) p) = p := rfl

/-- Every local coefficient is the indicated original cubic at the normalized
projective representative; thus the algebraic and bundle constructions agree. -/
theorem cubicSections_coefficient (k : Fin 4) (i : Index) (p : Total) :
    (cubicSections k).coefficient i p =
      let v := FailureOfSemipositiveMetricExtension.ProjectivePlane.vector i.1
        (FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates i.1 (blowdown p))
      ![FailureOfSemipositiveMetricExtension.Cubics.g₁ (v 0) (v 1) (v 2),
        FailureOfSemipositiveMetricExtension.Cubics.g₂ (v 0) (v 1) (v 2),
        FailureOfSemipositiveMetricExtension.Cubics.g₃ (v 0) (v 1) (v 2),
        FailureOfSemipositiveMetricExtension.Cubics.g₄ (v 0) (v 1) (v 2)] k := rfl

/-- The actual local bundle coordinates have exactly these cubic coefficients. -/
theorem cubicSections_localTriv (k : Fin 4) (i : Index) (p : Total)
    (hp : p ∈ baseSet i) :
    (core 3 (fun _ => 0)).localTriv i (sectionMap (cubicSections k) p) =
      (p,(cubicSections k).coefficient i p) := sectionMap_localTriv _ _ _ hp

end
end FailureOfSemipositiveMetricExtension.GlobalLineBundle
