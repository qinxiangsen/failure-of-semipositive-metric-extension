import FailureOfSemipositiveMetricExtension.HyperplaneCurveGeometry

/-! The actual fixed-fibre blowdown has a genuine analytic local inverse away
from the centres. This is proved in the installed incidence-surface atlas. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiber
noncomputable section
open Set Topology IsManifold
open scoped Manifold ContDiff

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]

theorem contMDiffAt_of_structural_maps (t : ℂ) (I : ModelWithCorners ℂ E H) (n : WithTop ℕ∞)
    {g : M → Fiber t} {x : M}
    (hb : ContMDiffAt I 𝓘(ℂ,ℂ × ℂ) n (fun y => blowdown t (g y)) x)
    (hd : ∀ r, ContMDiffAt I 𝓘(ℂ) n (fun y => direction t r (g y)) x) :
    ContMDiffAt I 𝓘(ℂ,Coord) n g x := by
  have hg : ContinuousAt g x :=
    (hb.continuousAt.prodMk (continuousAt_pi.mpr (fun r => (hd r).continuousAt))).codRestrict _
  obtain ⟨⟨r,e⟩,hx⟩ := charts_cover t (g x)
  have hmem := (mem_chartSource_iff r e (inclusion t (g x))).mp hx
  have hbase := ((ProjectivePlaneBundle.coordinates_contMDiffOn (baseChart r) n).contMDiffAt
    ((ProjectivePlane.chartSet_isOpen (baseChart r)).mem_nhds hmem.1)).comp x hb
  have hvec := (normalizedVector_contDiff (baseChart r) n).contMDiff.contMDiffAt.comp x hbase
  have hpair := (pairMap_contDiff r n).contMDiff.contMDiffAt.comp x
    ((contMDiffAt_const (c := t)).prodMk_space hvec)
  have hrad := (radialCoordinate_contDiff e n).contMDiff.contMDiffAt.comp x hpair
  have hdir := ((ProjectiveLineBundle.coordinates_contMDiffOn e n).contMDiffAt
    ((ProjectiveLine.chartSet_isOpen e).mem_nhds hmem.2.1)).comp x (hd r)
  have hcoord : ContMDiffAt I 𝓘(ℂ,Coord) n (fun y => structuralCoordinates t r e (g y)) x :=
    hrad.prodMk_space hdir
  have hq : structuralCoordinates t r e (g x) ∈ domain t r e := by
    rw [structuralCoordinates_eq t r e (g x) hx]
    exact (chart t r e).map_source hx
  have hparam := (param_contMDiffOn t r e n).contMDiffAt ((domain_isOpen t r e).mem_nhds hq)
  apply (hparam.comp x hcoord).congr_of_eventuallyEq
  filter_upwards [hg.eventually ((source_isOpen t r e).mem_nhds hx)] with y hy
  change g y = param t r e (structuralCoordinates t r e (g y))
  rw [structuralCoordinates_eq t r e (g y) hy,param_coordinates t r e (g y) hy]

/-- Canonical lift to the actual fixed fibre. -/
def awayLift (t : ℂ) (q : PlanePoint) : Fiber t :=
  ⟨(q,fun r => chosenDirection q r t),fun r => chosenDirection_incidence q r t⟩

@[simp] theorem blowdown_awayLift (t : ℂ) (q : PlanePoint) : blowdown t (awayLift t q) = q := rfl

theorem awayLift_blowdown (t : ℂ) (p : Fiber t) (hp : ∀ r, blowdown t p ≠ centre r t) :
    awayLift t (blowdown t p) = p := by
  apply inclusion_injective t
  apply total_ext
  · rfl
  · funext r
    exact directions_eq_away _ _ r rfl rfl (hp r)
  · rfl

theorem awayLift_contMDiffAt (t : ℂ) (n : WithTop ℕ∞) (q : PlanePoint)
    (hq : ∀ r, q ≠ centre r t) : ContMDiffAt 𝓘(ℂ,ℂ × ℂ) 𝓘(ℂ,Coord) n (awayLift t) q := by
  apply contMDiffAt_of_structural_maps t 𝓘(ℂ,ℂ × ℂ) n contMDiffAt_id
  intro r
  exact (BlowdownComplement.chosenDirection_contMDiffAt r n (q,t) (hq r)).comp q
    (contMDiffAt_id.prodMk contMDiffAt_const)

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiber
