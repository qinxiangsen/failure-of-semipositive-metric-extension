import FailureOfSemipositiveMetricExtension.GlobalFiberHomogeneousSections
import FailureOfSemipositiveMetricExtension.GlobalFiberExceptional
import FailureOfSemipositiveMetricExtension.BlowupSections

/-! The exact divided central cubic polynomials in the eight genuine fibre
charts, and their actual no-common-zero statement on the chart domains. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set
open scoped ContDiff

def centralMultiplicity (r : Fin 4) : ℕ := if r = 3 then 2 else 1

def cubicLocalCoefficient (r : Fin 4) (e : Fin 2) (k : Fin 4) (q : FixedFiber.Coord) : ℂ :=
  match r with
  | 0 => if e = 0 then FailureOfSemipositiveMetricExtension.BlowupSections.x₁ q.1 q.2 k else FailureOfSemipositiveMetricExtension.BlowupSections.y₁ q.1 q.2 k
  | 1 => if e = 0 then FailureOfSemipositiveMetricExtension.BlowupSections.x₂ q.1 q.2 k else FailureOfSemipositiveMetricExtension.BlowupSections.y₂ q.1 q.2 k
  | 2 => if e = 0 then FailureOfSemipositiveMetricExtension.BlowupSections.x₃ q.1 q.2 k else FailureOfSemipositiveMetricExtension.BlowupSections.y₃ q.1 q.2 k
  | 3 => if e = 0 then FailureOfSemipositiveMetricExtension.BlowupSections.x₄ q.1 q.2 k else FailureOfSemipositiveMetricExtension.BlowupSections.y₄ q.1 q.2 k

theorem cubicLocalCoefficient_contDiff (r : Fin 4) (e : Fin 2) (k : Fin 4) :
    ContDiff ℂ ω (cubicLocalCoefficient r e k) := by
  change ContDiff ℂ ω (fun q => cubicLocalCoefficient r e k q)
  fin_cases r <;> fin_cases e <;> fin_cases k <;>
    dsimp [cubicLocalCoefficient,FailureOfSemipositiveMetricExtension.BlowupSections.x₁,FailureOfSemipositiveMetricExtension.BlowupSections.y₁,
      FailureOfSemipositiveMetricExtension.BlowupSections.x₂,FailureOfSemipositiveMetricExtension.BlowupSections.y₂,
      FailureOfSemipositiveMetricExtension.BlowupSections.x₃,FailureOfSemipositiveMetricExtension.BlowupSections.y₃,
      FailureOfSemipositiveMetricExtension.BlowupSections.x₄,FailureOfSemipositiveMetricExtension.BlowupSections.y₄] <;> fun_prop

theorem cubic_divided_pullback (r : Fin 4) (e : Fin 2) (k : Fin 4) (q : FixedFiber.Coord) :
    (FailureOfSemipositiveMetricExtension.GlobalLineBundle.cubicGenerators k).value
      (0,baseVector r 0 (Blowup.projection (localParam e q))) =
      q.1 ^ centralMultiplicity r * cubicLocalCoefficient r e k q := by
  fin_cases r <;> fin_cases e <;> fin_cases k <;>
    dsimp [FailureOfSemipositiveMetricExtension.GlobalLineBundle.cubicGenerators,
      FailureOfSemipositiveMetricExtension.Cubics.g₁,FailureOfSemipositiveMetricExtension.Cubics.g₂,FailureOfSemipositiveMetricExtension.Cubics.g₃,FailureOfSemipositiveMetricExtension.Cubics.g₄,
      baseVector,localParam,Blowup.projection,Blowup.X,Blowup.Y,centralMultiplicity,
      cubicLocalCoefficient,FailureOfSemipositiveMetricExtension.BlowupSections.x₁,FailureOfSemipositiveMetricExtension.BlowupSections.y₁,
      FailureOfSemipositiveMetricExtension.BlowupSections.x₂,FailureOfSemipositiveMetricExtension.BlowupSections.y₂,
      FailureOfSemipositiveMetricExtension.BlowupSections.x₃,FailureOfSemipositiveMetricExtension.BlowupSections.y₃,
      FailureOfSemipositiveMetricExtension.BlowupSections.x₄,FailureOfSemipositiveMetricExtension.BlowupSections.y₄] <;> ring

theorem centralCubicSections_param (k : Fin 4) (d : DivisionIndex) (q : FixedFiber.Coord) :
    (centralCubicSections k).coefficient (divisionFrame d) (FixedFiber.param 0 d.1 d.2.1 q) =
      q.1 ^ centralMultiplicity d.1 * cubicLocalCoefficient d.1 d.2.1 k q := by
  rw [show (centralCubicSections k).coefficient (divisionFrame d) (FixedFiber.param 0 d.1 d.2.1 q) =
      (FailureOfSemipositiveMetricExtension.GlobalLineBundle.cubicGenerators k).value
        (0,baseVector d.1 0 (Blowup.projection (localParam d.2.1 q))) from
    homogeneousSection_coefficient_param 0 _ _ _ _ _ rfl]
  exact cubic_divided_pullback _ _ _ _

/-- After the verified radial powers are removed, the four polynomials have no common zero
on the actual chart domain, including all exceptional points. -/
theorem cubicLocalCoefficient_no_common_zero (r : Fin 4) (e : Fin 2) (q : FixedFiber.Coord)
    (hq : q ∈ FixedFiber.domain 0 r e) : ∃ k, cubicLocalCoefficient r e k q ≠ 0 := by
  classical
  by_contra hn
  push_neg at hn
  by_cases hr : q.1 = 0
  · fin_cases r <;> fin_cases e
    · have h := hn 3
      norm_num [cubicLocalCoefficient,FailureOfSemipositiveMetricExtension.BlowupSections.x₁,hr,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail] at h
    · have h := hn 0
      norm_num [cubicLocalCoefficient,FailureOfSemipositiveMetricExtension.BlowupSections.y₁,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail] at h
    · have h := hn 3
      norm_num [cubicLocalCoefficient,FailureOfSemipositiveMetricExtension.BlowupSections.x₂,hr,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail] at h
    · have h := hn 2
      norm_num [cubicLocalCoefficient,FailureOfSemipositiveMetricExtension.BlowupSections.y₂,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail] at h
    · have h := hn 3
      norm_num [cubicLocalCoefficient,FailureOfSemipositiveMetricExtension.BlowupSections.x₃,hr,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail] at h
    · have h := hn 0
      norm_num [cubicLocalCoefficient,FailureOfSemipositiveMetricExtension.BlowupSections.y₃,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail] at h
    · have h := hn 0
      norm_num [cubicLocalCoefficient,FailureOfSemipositiveMetricExtension.BlowupSections.x₄,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail] at h
    · have h := hn 2
      norm_num [cubicLocalCoefficient,FailureOfSemipositiveMetricExtension.BlowupSections.y₄,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail] at h
  · let v := baseVector r 0 (Blowup.projection (localParam e q))
    have hz (k : Fin 4) : (FailureOfSemipositiveMetricExtension.GlobalLineBundle.cubicGenerators k).value (0,v) = 0 := by
      rw [show v = baseVector r 0 (Blowup.projection (localParam e q)) from rfl,
        cubic_divided_pullback,hn k,mul_zero]
    have hzeros : FailureOfSemipositiveMetricExtension.Cubics.g₁ (v 0) (v 1) (v 2) = 0 ∧
        FailureOfSemipositiveMetricExtension.Cubics.g₂ (v 0) (v 1) (v 2) = 0 ∧
        FailureOfSemipositiveMetricExtension.Cubics.g₃ (v 0) (v 1) (v 2) = 0 ∧
        FailureOfSemipositiveMetricExtension.Cubics.g₄ (v 0) (v 1) (v 2) = 0 := ⟨hz 0,hz 1,hz 2,hz 3⟩
    have hc := (FailureOfSemipositiveMetricExtension.Coordinates.projective_cubic_common_zero_locus v
      (baseVector_ne_zero r 0 _)).mp hzeros
    have haway := (FixedFiber.param_mem_awayCentres_iff 0 r e q hq).mpr hr
    rcases hc with h | h | h | h
    · exact haway 0 h
    · exact haway 1 h
    · exact haway 2 h
    · exact haway 3 h
end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
