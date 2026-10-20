import FailureOfSemipositiveMetricExtension.CentralCurveDegreeBundles
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! The actual differential of the defining divisor section along its zero
curve, in genuine line frames. At a zero its transformation is exactly the
original divisor cocycle; the derivative-of-gain term vanishes. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.CurveNormal
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

abbrev AmbientTangent (d : Direction) := TangentSpace 𝓘(ℂ,FixedFiber.Coord) (lineParam d)

def tangentMap (d : Direction) : TangentSpace 𝓘(ℂ) d →L[ℂ] AmbientTangent d :=
  mfderiv 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) lineParam d

def tangentImage (d : Direction) : Submodule ℂ (AmbientTangent d) :=
  LinearMap.range (tangentMap d).toLinearMap

/-- The normal fibre is the actual tangent-space quotient by the actual tangent
image. No scalar replacement is used in this definition. -/
abbrev NormalFiber (d : Direction) := AmbientTangent d ⧸ tangentImage d

def frameDerivative (i : Index) (d : Direction) : AmbientTangent d →L[ℂ] ℂ :=
  mfderiv 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) (ellSection.coefficient i) (lineParam d)

theorem coefficient_zero (i : Index) (d : Direction) (hi : lineParam d ∈ baseSet 0 i) :
    ellSection.coefficient i (lineParam d) = 0 :=
  (sectionValue_zero_iff ellSection i (lineParam d) hi).mp (ellSection_lineParam_zero d)

theorem frameDerivative_transition (i j : Index) (d : Direction)
    (hi : lineParam d ∈ baseSet 0 i) (hj : lineParam d ∈ baseSet 0 j) :
    frameDerivative j d = gain 0 (-2) ellDegree i j (lineParam d) • frameDerivative i d := by
  let p := lineParam d
  have hgain := ((gain_contMDiffOn 0 (-2) ellDegree i j ω).contMDiffAt
    (((baseSet_isOpen 0 i).inter (baseSet_isOpen 0 j)).mem_nhds ⟨hi,hj⟩)).mdifferentiableAt
      (show (1 : WithTop ℕ∞) ≤ ω from le_top)
  have hfi := ((ellSection.analytic i).contMDiffAt ((baseSet_isOpen 0 i).mem_nhds hi)).mdifferentiableAt
    (show (1 : WithTop ℕ∞) ≤ ω from le_top)
  have he : (gain 0 (-2) ellDegree i j * ellSection.coefficient i) =ᶠ[𝓝 p]
      ellSection.coefficient j := by
    filter_upwards [((baseSet_isOpen 0 i).inter (baseSet_isOpen 0 j)).mem_nhds ⟨hi,hj⟩] with q hq
    exact ellSection.compatible i j q hq
  have hprod := (hgain.hasMFDerivAt.mul hfi.hasMFDerivAt).mfderiv
  change mfderiv 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) (ellSection.coefficient j) p = _
  rw [← he.mfderiv_eq,hprod]
  rw [coefficient_zero i d hi]
  ext v
  change gain 0 (-2) ellDegree i j (lineParam d) * frameDerivative i d v +
    (0 : ℂ) * (show ℂ from mfderiv 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) (gain 0 (-2) ellDegree i j) (lineParam d) v) =
    gain 0 (-2) ellDegree i j (lineParam d) * frameDerivative i d v
  ring

/-- The differential annihilates the actual tangent image, by differentiating
its identically zero restriction on a genuine open frame neighbourhood. -/
theorem frameDerivative_tangentMap (i : Index) (d : Direction)
    (hi : lineParam d ∈ baseSet 0 i) (v : TangentSpace 𝓘(ℂ) d) :
    frameDerivative i d (tangentMap d v) = 0 := by
  have hfi := ((ellSection.analytic i).contMDiffAt ((baseSet_isOpen 0 i).mem_nhds hi)).mdifferentiableAt
    (show (1 : WithTop ℕ∞) ≤ ω from le_top)
  have hline := ((lineParam_contMDiff 1) d).mdifferentiableAt le_rfl
  have he : (ellSection.coefficient i ∘ lineParam) =ᶠ[𝓝 d] fun _ => (0 : ℂ) := by
    filter_upwards [((baseSet_isOpen 0 i).preimage lineParam_continuous).mem_nhds hi] with q hq
    exact coefficient_zero i q hq
  have h := mfderiv_comp_apply d hfi hline v
  rw [he.mfderiv_eq,mfderiv_const] at h
  exact h.symm

theorem tangentImage_le_ker (i : Index) (d : Direction)
    (hi : lineParam d ∈ baseSet 0 i) : tangentImage d ≤ LinearMap.ker (frameDerivative i d).toLinearMap := by
  rintro v ⟨w,rfl⟩
  exact frameDerivative_tangentMap i d hi w

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.CurveNormal
