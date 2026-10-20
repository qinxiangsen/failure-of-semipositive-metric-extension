import FailureOfSemipositiveMetricExtension.CentralCurveNormalDerivative
import FailureOfSemipositiveMetricExtension.FixedFiberCanonicalTangentForms
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-! The actual defining-section differential is surjective at every point of
its smooth zero curve, proved from the verified slope-times-unit formula. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.CurveNormal
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

def slope (j : DivisionIndex) (p : GlobalIncidence.Fiber 0) : ℂ :=
  (FixedFiber.coordinates 0 j.1 j.2.1 p).2

theorem slope_mdifferentiableAt (j : DivisionIndex) (p : GlobalIncidence.Fiber 0)
    (hp : p ∈ FixedFiber.source 0 j.1 j.2.1) :
    MDifferentiableAt 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) (slope j) p :=
  ((ContinuousLinearMap.snd ℂ ℂ ℂ).differentiableAt.mdifferentiableAt).comp p
    (((FixedFiber.coordinates_contMDiffOn 0 j.1 j.2.1 1).contMDiffAt
      ((FixedFiber.source_isOpen 0 j.1 j.2.1).mem_nhds hp)).mdifferentiableAt le_rfl)

theorem slope_mfderiv (j : DivisionIndex) (p : GlobalIncidence.Fiber 0)
    (hp : p ∈ FixedFiber.source 0 j.1 j.2.1)
    (v : TangentSpace 𝓘(ℂ,FixedFiber.Coord) p) :
    mfderiv 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) (slope j) p v =
      (FixedFiber.chartTangentEquiv 0 j.1 j.2.1 p hp v).2 := by
  have hc := ((FixedFiber.coordinates_contMDiffOn 0 j.1 j.2.1 1).contMDiffAt
    ((FixedFiber.source_isOpen 0 j.1 j.2.1).mem_nhds hp)).mdifferentiableAt le_rfl
  have h := mfderiv_comp_apply p
    ((ContinuousLinearMap.snd ℂ ℂ ℂ).differentiableAt.mdifferentiableAt) hc v
  rw [mfderiv_eq_fderiv,ContinuousLinearMap.fderiv] at h
  exact h

/-- In each valid simple-zero frame, dℓ is its nonzero analytic unit times the
actual transverse chart differential. -/
theorem frameDerivative_simple (j : DivisionIndex) (d : Direction)
    (hj : lineParam d ∈ divisionPatch 0 j) (v : AmbientTangent d) :
    frameDerivative (divisionFrame j) d v = ellLocalUnit j (lineParam d) *
      (FixedFiber.chartTangentEquiv 0 j.1 j.2.1 (lineParam d) hj.1 v).2 := by
  have hdata := lineParam_chart_data d j.1 j.2.1 hj.1
  have hs := slope_mdifferentiableAt j (lineParam d) hj.1
  have hu := ((ellLocalUnit_contMDiffOn j).contMDiffAt
    ((divisionPatch_isOpen 0 j).mem_nhds hj)).mdifferentiableAt (show (1 : WithTop ℕ∞) ≤ ω from le_top)
  have he : (ellSection.coefficient (divisionFrame j)) =ᶠ[𝓝 (lineParam d)]
      slope j * ellLocalUnit j := by
    filter_upwards [(divisionPatch_isOpen 0 j).mem_nhds hj] with q hq
    exact ellSection_coefficient_simple j hdata.1 hdata.2.1 q hq
  have hz : slope j (lineParam d) = 0 := hdata.2.2
  have hprod := (hs.hasMFDerivAt.mul hu.hasMFDerivAt).mfderiv
  unfold frameDerivative
  rw [he.mfderiv_eq,hprod,hz]
  change (0 : ℂ) * (show ℂ from mfderiv 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) (ellLocalUnit j) (lineParam d) v) +
    ellLocalUnit j (lineParam d) * (show ℂ from mfderiv 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) (slope j) (lineParam d) v) = _
  rw [zero_mul,zero_add,slope_mfderiv j (lineParam d) hj.1 v]

/-- An explicit actual tangent lift realizes every transverse derivative value. -/
theorem frameDerivative_simple_surjective (j : DivisionIndex) (d : Direction)
    (hj : lineParam d ∈ divisionPatch 0 j) :
    Function.Surjective (frameDerivative (divisionFrame j) d) := by
  intro z
  refine ⟨(FixedFiber.chartTangentEquiv 0 j.1 j.2.1 (lineParam d) hj.1).symm
    (0,z / ellLocalUnit j (lineParam d)),?_⟩
  rw [frameDerivative_simple j d hj,ContinuousLinearEquiv.apply_symm_apply]
  exact mul_div_cancel₀ z (ellLocalUnit_ne_zero j (lineParam d) hj)

/-- Surjectivity holds in every actual ambient line frame, not only a selected
simple-zero frame. -/
theorem frameDerivative_surjective (i : Index) (d : Direction)
    (hi : lineParam d ∈ baseSet 0 i) : Function.Surjective (frameDerivative i d) := by
  obtain ⟨j,hj⟩ := divisionPatch_cover 0 (lineParam d)
  have hg : gain 0 (-2) ellDegree (divisionFrame j) i (lineParam d) ≠ 0 := by
    intro hz
    have hcomp := gain_comp 0 (-2) ellDegree (divisionFrame j) i (divisionFrame j)
      (lineParam d) ⟨⟨hj.2,hi⟩,hj.2⟩
    rw [hz,mul_zero,gain_self] at hcomp
    exact zero_ne_one hcomp
  intro z
  obtain ⟨v,hv⟩ := frameDerivative_simple_surjective j d hj
    (z / gain 0 (-2) ellDegree (divisionFrame j) i (lineParam d))
  refine ⟨v,?_⟩
  rw [frameDerivative_transition (divisionFrame j) i d hj.2 hi,
    ContinuousLinearMap.smul_apply,smul_eq_mul,hv]
  exact mul_div_cancel₀ z hg

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.CurveNormal
