import FailureOfSemipositiveMetricExtension.FixedFiberCanonicalFactors

/-! Exact identification of the canonical Jacobian cocycle with the actual
ambient degree (1;-1,-1,-1,-1), through nowhere-zero analytic local factors. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle Topology
open ComplexSurfaceJacobian
open scoped Manifold ContDiff

/-- The blow-down chain rule expressed in the existing homogeneous ratio. -/
theorem chartJacobian_radial_identity (t : ℂ) (d c : DivisionIndex) (p : Fiber t)
    (hd : p ∈ divisionPatch t d) (hc : p ∈ divisionPatch t c) :
    (directionSign c.2.1 * (FixedFiber.coordinates t c.1 c.2.1 p).1) *
      FixedFiber.chartJacobian t d.1 c.1 d.2.1 c.2.1 p =
    (planeSign (baseChart d.1) * planeSign (baseChart c.1) *
      FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle.ratio (baseChart d.1) (baseChart c.1)
        (FixedFiber.blowdown t p) ^ 3) *
      (directionSign d.2.1 * (FixedFiber.coordinates t d.1 d.2.1 p).1) := by
  have hq := FixedFiber.coordinates_mem_changeDomain t d.1 c.1 d.2.1 c.2.1 p hd.1 hc.1
  have h := FixedFiber.change_jacobian_blowdown t d.1 c.1 d.2.1 c.2.1 _ hq
  have heq : FixedFiber.change t d.1 c.1 d.2.1 c.2.1 (FixedFiber.coordinates t d.1 d.2.1 p) =
      FixedFiber.coordinates t c.1 c.2.1 p := by
    change FixedFiber.coordinates t c.1 c.2.1
      (FixedFiber.param t d.1 d.2.1 (FixedFiber.coordinates t d.1 d.2.1 p)) = _
    rw [FixedFiber.param_coordinates t d.1 d.2.1 p hd.1]
  rw [heq,FixedFiber.baseMap_coordinates t d.1 d.2.1 p hd.1] at h
  have hrat := FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle.ratio_comp (baseChart c.1) (baseChart d.1)
    (baseChart c.1) (FixedFiber.blowdown t p) hd.2.1 hc.2.1
  rw [FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle.ratio_self] at hrat
  have hi := eq_inv_of_mul_eq_one_left hrat
  change FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle.ratio (baseChart d.1) (baseChart c.1) (FixedFiber.blowdown t p) =
    (ProjectivePlane.vector (baseChart d.1) (ProjectivePlane.coordinates (baseChart d.1) (FixedFiber.blowdown t p)) (baseChart c.1))⁻¹ at hi
  rw [← inv_pow,← hi] at h
  exact h

/-- On the nonexceptional locus the specific K identification follows by scalar cancellation. -/
theorem canonicalFactor_jacobian_away (t : ℂ) (d c : DivisionIndex) (p : Fiber t)
    (hd : p ∈ divisionPatch t d) (hc : p ∈ divisionPatch t c) (hp : p ∈ FixedFiber.awayCentres t) :
    gain t 1 (fun _ => -1) (divisionFrame d) (divisionFrame c) p * canonicalFactor t c p *
      FixedFiber.chartJacobian t d.1 c.1 d.2.1 c.2.1 p = canonicalFactor t d p := by
  have hE := (pullback t FailureOfSemipositiveMetricExtension.GlobalLineBundle.exceptionalProduct).compatible
    (divisionFrame d) (divisionFrame c) p ⟨hd.2,hc.2⟩
  rw [exceptionalGain_canonicalGain,exceptionalProduct_radial t d p hd,
    exceptionalProduct_radial t c p hc] at hE
  have hJ := chartJacobian_radial_identity t d c p hd hc
  have hr : (FixedFiber.coordinates t c.1 c.2.1 p).1 ≠ 0 := by
    intro hz
    have he : exceptionalCoefficient t c.1 (divisionFrame c) p = 0 := by
      conv_lhs => rw [← FixedFiber.param_coordinates t c.1 c.2.1 p hc.1]
      rw [exceptionalCoefficient_param,hz]
    exact hp c.1 ((exceptionalCoefficient_zero_iff t c.1 (divisionFrame c) p hc.2).mp he)
  apply canonical_factor_algebra _ _ _ _ _ _ _ _ _ _ _ _
    (canonicalOthers_ne_zero t d p hd) (canonicalOthers_ne_zero t c p hc) hr _ hJ
  · simp only [planeSign]
    split <;> norm_num
  · convert hE using 1 <;> dsimp only [divisionFrame,FailureOfSemipositiveMetricExtension.GlobalLineBundle.divisionFrame] <;> ring

/-- The identity extends to every exceptional point by the proved density theorem. -/
theorem canonicalFactor_jacobian (t : ℂ) (d c : DivisionIndex) (p : Fiber t)
    (hd : p ∈ divisionPatch t d) (hc : p ∈ divisionPatch t c) :
    gain t 1 (fun _ => -1) (divisionFrame d) (divisionFrame c) p * canonicalFactor t c p *
      FixedFiber.chartJacobian t d.1 c.1 d.2.1 c.2.1 p = canonicalFactor t d p := by
  let U := divisionPatch t d ∩ divisionPatch t c
  have hU : IsOpen U := (divisionPatch_isOpen t d).inter (divisionPatch_isOpen t c)
  have hg := (gain_contMDiffOn t 1 (fun _ => -1) (divisionFrame d) (divisionFrame c) ω).continuousOn.mono
    (show U ⊆ baseSet t (divisionFrame d) ∩ baseSet t (divisionFrame c) from fun _ h => ⟨h.1.2,h.2.2⟩)
  have hf := (canonicalFactor_contMDiffOn t c).continuousOn.mono (show U ⊆ divisionPatch t c from inter_subset_right)
  have hj := (FixedFiber.chartJacobian_contMDiffOn t d.1 c.1 d.2.1 c.2.1).continuousOn.mono
    (show U ⊆ FixedFiber.source t d.1 d.2.1 ∩ FixedFiber.source t c.1 c.2.1 from fun _ h => ⟨h.1.1,h.2.1⟩)
  have ht := (canonicalFactor_contMDiffOn t d).continuousOn.mono (show U ⊆ divisionPatch t d from inter_subset_left)
  have he : EqOn
      (fun q => gain t 1 (fun _ => -1) (divisionFrame d) (divisionFrame c) q * canonicalFactor t c q *
        FixedFiber.chartJacobian t d.1 c.1 d.2.1 c.2.1 q)
      (canonicalFactor t d) (U ∩ FixedFiber.awayCentres t) := by
    intro q hq
    exact canonicalFactor_jacobian_away t d c q hq.1.1 hq.1.2 hq.2
  exact he.of_subset_closure ((hg.mul hf).mul hj) ht inter_subset_left
    ((FixedFiber.awayCentres_dense t).open_subset_closure_inter hU) ⟨hd,hc⟩

def divisionChart (d : DivisionIndex) : FixedFiber.CanonicalIndex := (d.1,d.2.1)

/-- The same identity in the coefficient-transition direction used by the canonical core. -/
theorem canonicalFactor_transition (t : ℂ) (d c : DivisionIndex) (p : Fiber t)
    (hd : p ∈ divisionPatch t d) (hc : p ∈ divisionPatch t c) :
    FixedFiber.canonicalGain t (divisionChart d) (divisionChart c) p * canonicalFactor t d p =
      gain t 1 (fun _ => -1) (divisionFrame d) (divisionFrame c) p * canonicalFactor t c p := by
  rw [← canonicalFactor_jacobian t d c p hd hc]
  change FixedFiber.chartJacobian t c.1 d.1 c.2.1 d.2.1 p *
    (gain t 1 (fun _ => -1) (divisionFrame d) (divisionFrame c) p * canonicalFactor t c p *
      FixedFiber.chartJacobian t d.1 c.1 d.2.1 c.2.1 p) = _
  calc
    _ = (FixedFiber.chartJacobian t c.1 d.1 c.2.1 d.2.1 p *
      FixedFiber.chartJacobian t d.1 c.1 d.2.1 c.2.1 p) *
      (gain t 1 (fun _ => -1) (divisionFrame d) (divisionFrame c) p * canonicalFactor t c p) := by ring
    _ = _ := by
      rw [FixedFiber.chartJacobian_cocycle t d.1 c.1 d.1 d.2.1 c.2.1 d.2.1 p hd.1 hc.1 hd.1,
        FixedFiber.chartJacobian_self,one_mul]

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
