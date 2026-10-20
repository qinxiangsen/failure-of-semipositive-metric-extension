import FailureOfSemipositiveMetricExtension.GlobalExceptionalSection

/-! Homogeneous polynomial data give genuine analytic sections on the actual
family by pullback from the projective plane. These sections are not yet divided
by exceptional divisor sections. -/
namespace FailureOfSemipositiveMetricExtension.GlobalLineBundle
noncomputable section
open Set Bundle IsManifold FailureOfSemipositiveMetricExtension.GlobalIncidence
open scoped Manifold ContDiff

structure HomogeneousData (d : ℤ) where
  value : ℂ × (Fin 3 → ℂ) → ℂ
  analytic : ContDiff ℂ ω value
  homogeneous : ∀ (t c : ℂ) (v : Fin 3 → ℂ), value (t,c • v) = c ^ d * value (t,v)

def homogeneousCoefficient {d : ℤ} (f : HomogeneousData d) (i : Index) (p : Total) : ℂ :=
  f.value (projection p,FailureOfSemipositiveMetricExtension.ProjectivePlane.vector i.1
    (FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates i.1 (blowdown p)))

theorem homogeneousCoefficient_transition {d : ℤ} (f : HomogeneousData d)
    (i j : Index) (p : Total) (hp : p ∈ baseSet i ∩ baseSet j) :
    gain d (fun _ => 0) i j p * homogeneousCoefficient f i p = homogeneousCoefficient f j p := by
  simp only [gain,FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.gain,zpow_zero,Finset.prod_const_one,mul_one]
  unfold homogeneousCoefficient
  rw [normalizedVector_change i.1 j.1 (blowdown p) hp.1.1 hp.2.1,f.homogeneous]
  rfl

theorem homogeneousCoefficient_contMDiffOn {d : ℤ} (f : HomogeneousData d) (i : Index) :
    ContMDiffOn 𝓘(ℂ,ChartCoord) 𝓘(ℂ) ω (homogeneousCoefficient f i) (baseSet i) := by
  have hv : ContDiff ℂ ω (FailureOfSemipositiveMetricExtension.ProjectivePlane.vector i.1) := by
    apply contDiff_pi.mpr
    intro j
    rcases i with ⟨a,b⟩
    fin_cases a <;> fin_cases j <;> dsimp [FailureOfSemipositiveMetricExtension.ProjectivePlane.vector] <;> fun_prop
  have hc := (FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle.coordinates_contMDiffOn i.1 ω).comp
    (blowdown_contMDiff ω).contMDiffOn (s := baseSet i) (fun _ hp => hp.1)
  exact f.analytic.contMDiff.comp_contMDiffOn
    ((projection_contMDiff ω).contMDiffOn.prodMk_space (hv.contMDiff.comp_contMDiffOn hc))

def homogeneousSection {d : ℤ} (f : HomogeneousData d) : SectionData d (fun _ => 0) where
  coefficient := homogeneousCoefficient f
  analytic := homogeneousCoefficient_contMDiffOn f
  compatible := homogeneousCoefficient_transition f

def pencilHomogeneous (k : Fin 2) : HomogeneousData 2 where
  value q := if k = 0 then FailureOfSemipositiveMetricExtension.Coordinates.F₁ q.1 (q.2 0) (q.2 1) (q.2 2)
    else FailureOfSemipositiveMetricExtension.Coordinates.F₂ q.1 (q.2 0) (q.2 1) (q.2 2)
  analytic := by fin_cases k <;> dsimp [FailureOfSemipositiveMetricExtension.Coordinates.F₁,FailureOfSemipositiveMetricExtension.Coordinates.F₂] <;> fun_prop
  homogeneous t c v := by
    fin_cases k <;> simp [FailureOfSemipositiveMetricExtension.Coordinates.F₁,FailureOfSemipositiveMetricExtension.Coordinates.F₂,Pi.smul_apply,smul_eq_mul,zpow_ofNat] <;> ring

/-- The actual degree-two pencil before its verified exceptional division. -/
def pulledBackPencil (k : Fin 2) : SectionData 2 (fun _ => 0) := homogeneousSection (pencilHomogeneous k)

theorem pulledBackPencil_analytic (k : Fin 2) :
    ContMDiff 𝓘(ℂ,ChartCoord) (𝓘(ℂ,ChartCoord).prod 𝓘(ℂ)) ω
      (sectionMap (pulledBackPencil k)) := sectionMap_contMDiff _
end
end FailureOfSemipositiveMetricExtension.GlobalLineBundle
