import FailureOfSemipositiveMetricExtension.GlobalFiberManifold
import FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle
import FailureOfSemipositiveMetricExtension.ProjectiveLineBundle

/-! A map into the actual fixed incidence fibre is analytic when its genuine
projective structural components are analytic. The proof reconstructs its local
surface coordinates using the verified atlas; no embedding regularity is assumed. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiber
noncomputable section
open Set Topology IsManifold
open scoped Manifold ContDiff

def structuralCoordinates (t : ℂ) (r : Fin 4) (e : Fin 2) (p : Fiber t) : Coord :=
  (radialCoordinate e (pairMap r t (ProjectivePlane.vector (baseChart r)
    (ProjectivePlane.coordinates (baseChart r) (blowdown t p)))),
    ProjectiveLine.coordinates e (direction t r p))

theorem structuralCoordinates_eq (t : ℂ) (r : Fin 4) (e : Fin 2) (p : Fiber t)
    (hp : p ∈ source t r e) : structuralCoordinates t r e p = coordinates t r e p := by
  change _ = (chartCoordinates r e (inclusion t p)).1
  rw [chartCoordinates_eq_explicit r e (inclusion t p) hp]
  rfl

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]

theorem continuous_of_structural_maps (t : ℂ) {g : M → Fiber t}
    (hb : Continuous (fun x => blowdown t (g x)))
    (hd : ∀ r, Continuous (fun x => direction t r (g x))) : Continuous g :=
  (hb.prodMk (continuous_pi hd)).subtype_mk _

theorem structuralCoordinates_comp_contMDiffOn (t : ℂ) (I : ModelWithCorners ℂ E H)
    (n : WithTop ℕ∞) {g : M → Fiber t}
    (hb : ContMDiff I 𝓘(ℂ,ℂ × ℂ) n (fun x => blowdown t (g x)))
    (hd : ∀ r, ContMDiff I 𝓘(ℂ) n (fun x => direction t r (g x))) (r : Fin 4) (e : Fin 2) :
    ContMDiffOn I 𝓘(ℂ,Coord) n (fun x => structuralCoordinates t r e (g x))
      (g ⁻¹' source t r e) := by
  have hbase : ContMDiffOn I 𝓘(ℂ,ℂ × ℂ) n
      (fun x => ProjectivePlane.coordinates (baseChart r) (blowdown t (g x)))
      (g ⁻¹' source t r e) :=
    (ProjectivePlaneBundle.coordinates_contMDiffOn (baseChart r) n).comp hb.contMDiffOn
      (fun x hx => ((mem_chartSource_iff r e (inclusion t (g x))).mp hx).1)
  have hvec := (normalizedVector_contDiff (baseChart r) n).contMDiff.comp_contMDiffOn hbase
  have hp := (pairMap_contDiff r n).contMDiff.comp_contMDiffOn
    ((contMDiffOn_const (c := t)).prodMk_space hvec)
  have hr := (radialCoordinate_contDiff e n).contMDiff.comp_contMDiffOn hp
  have hs : ContMDiffOn I 𝓘(ℂ) n
      (fun x => ProjectiveLine.coordinates e (direction t r (g x))) (g ⁻¹' source t r e) :=
    (ProjectiveLineBundle.coordinates_contMDiffOn e n).comp (hd r).contMDiffOn
      (fun x hx => ((mem_chartSource_iff r e (inclusion t (g x))).mp hx).2.1)
  exact hr.prodMk_space hs

/-- This criterion constructs analytic local coordinates in the actual fibre;
it is stronger than merely assuming continuity into an algebraic incidence set. -/
theorem contMDiff_of_structural_maps (t : ℂ) (I : ModelWithCorners ℂ E H) (n : WithTop ℕ∞)
    {g : M → Fiber t}
    (hb : ContMDiff I 𝓘(ℂ,ℂ × ℂ) n (fun x => blowdown t (g x)))
    (hd : ∀ r, ContMDiff I 𝓘(ℂ) n (fun x => direction t r (g x))) :
    ContMDiff I 𝓘(ℂ,Coord) n g := by
  have hg := continuous_of_structural_maps t hb.continuous (fun r => (hd r).continuous)
  intro x
  obtain ⟨⟨r,e⟩,hx⟩ := charts_cover t (g x)
  have hU : IsOpen (g ⁻¹' source t r e) := (source_isOpen t r e).preimage hg
  have hq : structuralCoordinates t r e (g x) ∈ domain t r e := by
    rw [structuralCoordinates_eq t r e (g x) hx]
    exact (chart t r e).map_source hx
  have hparam := (param_contMDiffOn t r e n).contMDiffAt ((domain_isOpen t r e).mem_nhds hq)
  have hcoord := (structuralCoordinates_comp_contMDiffOn t I n hb hd r e).contMDiffAt (hU.mem_nhds hx)
  apply (hparam.comp x hcoord).congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hx] with y hy
  change g y = param t r e (structuralCoordinates t r e (g y))
  rw [structuralCoordinates_eq t r e (g y) hy,param_coordinates t r e (g y) hy]

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiber
