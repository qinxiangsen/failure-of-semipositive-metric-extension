import FailureOfSemipositiveMetricExtension.FixedFiberCanonicalAtlas
import FailureOfSemipositiveMetricExtension.CentralExceptionalProduct

/-! Nowhere-zero local canonical form factors on a genuine refinement of the
surface atlas.  The specific ambient multidegree is derived from actual Jacobians
and actual exceptional-section transition identities. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle Topology
open ComplexSurfaceJacobian
open scoped Manifold ContDiff

def canonicalOthers (t : ℂ) (d : DivisionIndex) (p : Fiber t) : ℂ :=
  ∏ r ∈ Finset.univ.erase d.1, exceptionalCoefficient t r (divisionFrame d) p

theorem canonicalOthers_ne_zero (t : ℂ) (d : DivisionIndex) (p : Fiber t)
    (hp : p ∈ divisionPatch t d) : canonicalOthers t d p ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro r hr
  exact fun hz => divisionPatch_avoids_other_centres t d p hp r (Finset.mem_erase.mp hr).1
    ((exceptionalCoefficient_zero_iff t r (divisionFrame d) p hp.2).mp hz)

theorem canonicalOthers_contMDiffOn (t : ℂ) (d : DivisionIndex) :
    ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω (canonicalOthers t d) (divisionPatch t d) := by
  apply scalarProduct_contMDiffOn
  intro r _
  exact (exceptionalCoefficient_contMDiffOn t r (divisionFrame d)).mono (divisionPatch_subset_frame t d)

/-- The local two-form multiplying an ambient K frame is sign/(the other three E coefficients). -/
def canonicalFactor (t : ℂ) (d : DivisionIndex) (p : Fiber t) : ℂ :=
  planeSign (baseChart d.1) * directionSign d.2.1 / canonicalOthers t d p

theorem canonicalFactor_ne_zero (t : ℂ) (d : DivisionIndex) (p : Fiber t)
    (hp : p ∈ divisionPatch t d) : canonicalFactor t d p ≠ 0 := by
  apply div_ne_zero _ (canonicalOthers_ne_zero t d p hp)
  apply mul_ne_zero _ (directionSign_ne_zero d.2.1)
  simp only [planeSign]
  split <;> norm_num

theorem canonicalFactor_contMDiffOn (t : ℂ) (d : DivisionIndex) :
    ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω (canonicalFactor t d) (divisionPatch t d) := by
  have hinv : ContDiffOn ℂ ω (fun z : ℂ => z⁻¹) {z | z ≠ 0} := contDiffOn_id.inv (fun _ h => h)
  have hi : ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω
      (fun p => (canonicalOthers t d p)⁻¹) (divisionPatch t d) :=
    hinv.contMDiffOn.comp (canonicalOthers_contMDiffOn t d) (fun p hp => canonicalOthers_ne_zero t d p hp)
  simpa only [canonicalFactor,div_eq_mul_inv,smul_eq_mul] using
    (contMDiffOn_const (c := planeSign (baseChart d.1) * directionSign d.2.1)).smul hi

theorem exceptionalProduct_radial (t : ℂ) (d : DivisionIndex) (p : Fiber t)
    (hp : p ∈ divisionPatch t d) :
    (pullback t FailureOfSemipositiveMetricExtension.GlobalLineBundle.exceptionalProduct).coefficient (divisionFrame d) p =
      (FixedFiber.coordinates t d.1 d.2.1 p).1 * canonicalOthers t d p := by
  have hE : exceptionalCoefficient t d.1 (divisionFrame d) p = (FixedFiber.coordinates t d.1 d.2.1 p).1 := by
    conv_lhs => rw [← FixedFiber.param_coordinates t d.1 d.2.1 p hp.1]
    exact exceptionalCoefficient_param t d _
  change (∏ r,exceptionalCoefficient t r (divisionFrame d) p) = _
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ d.1),hE]
  rfl

theorem exceptionalGain_canonicalGain (t : ℂ) (i j : Index) (p : Fiber t) :
    gain t 4 (fun _ => -1) i j p =
      FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle.ratio i.1 j.1 (FixedFiber.blowdown t p) ^ 3 *
        gain t 1 (fun _ => -1) i j p := by
  change FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle.ratio i.1 j.1 (FixedFiber.blowdown t p) ^ (4 : ℤ) * _ =
    _ * (FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle.ratio i.1 j.1 (FixedFiber.blowdown t p) ^ (1 : ℤ) * _)
  norm_num
  ring
  all_goals ac_rfl

/-- Pure scalar cancellation, with the sign and direction of the Jacobian fixed. -/
theorem canonical_factor_algebra (u v a b ri rj Oi Oj G R J : ℂ)
    (hv : v*v=1) (hOi : Oi ≠ 0) (hOj : Oj ≠ 0) (hrj : rj ≠ 0)
    (hE : G * R^3 * (ri*Oi) = rj*Oj)
    (hJ : (b*rj)*J = (u*v*R^3)*(a*ri)) :
    G*(v*b/Oj)*J = u*a/Oi := by
  apply (eq_div_iff hOi).mpr
  apply mul_right_cancel₀ hOj
  have hc : (G*(v*b)*J*Oi) = u*a*Oj := by
    apply mul_right_cancel₀ hrj
    calc
      (G*(v*b)*J*Oi)*rj = G*v*Oi*((b*rj)*J) := by ring
      _ = G*v*Oi*((u*v*R^3)*(a*ri)) := by rw [hJ]
      _ = u*a*(v*v)*(G*R^3*(ri*Oi)) := by ring
      _ = u*a*(rj*Oj) := by rw [hv,hE]; ring
      _ = (u*a*Oj)*rj := by ring
  calc
    (G*(v*b/Oj)*J*Oi)*Oj = G*(v*b)*J*Oi := by field_simp
    _ = (u*a)*Oj := hc

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
