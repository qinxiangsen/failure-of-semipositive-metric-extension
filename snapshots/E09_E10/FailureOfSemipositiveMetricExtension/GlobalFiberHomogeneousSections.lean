import FailureOfSemipositiveMetricExtension.GlobalFiberSections
import FailureOfSemipositiveMetricExtension.GlobalCubicSections

/-! Homogeneous data, and specifically the paper's four cubic generators, as
actual analytic H^d sections on the existing fixed fibres. These are the
undivided sections; exceptional division is a separate construction. -/

namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle
open scoped Manifold ContDiff

/-- Restriction of genuine homogeneous section data to a genuine fixed fibre. -/
def homogeneousSection (t : ℂ) {d : ℤ} (f : FailureOfSemipositiveMetricExtension.GlobalLineBundle.HomogeneousData d) :
    SectionData t d (fun _ => 0) := pullback t (FailureOfSemipositiveMetricExtension.GlobalLineBundle.homogeneousSection f)

theorem homogeneousSection_contMDiff (t : ℂ) {d : ℤ}
    (f : FailureOfSemipositiveMetricExtension.GlobalLineBundle.HomogeneousData d) :
    ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (sectionMap (homogeneousSection t f)) := sectionMap_contMDiff _

/-- The exact normalized homogeneous coefficient on the actual fibre. -/
theorem homogeneousSection_coefficient (t : ℂ) {d : ℤ}
    (f : FailureOfSemipositiveMetricExtension.GlobalLineBundle.HomogeneousData d) (i : Index) (p : Fiber t) :
    (homogeneousSection t f).coefficient i p =
      f.value (t,FailureOfSemipositiveMetricExtension.ProjectivePlane.vector i.1
        (FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates i.1 (FixedFiber.blowdown t p))) := rfl

/-- In the matching base block, the coefficient is evaluated at the actual centred
homogeneous vector used in the blow-up chart. -/
theorem homogeneousSection_coefficient_param (t : ℂ) {d : ℤ}
    (f : FailureOfSemipositiveMetricExtension.GlobalLineBundle.HomogeneousData d) (c : Fin 4) (e : Fin 2)
    (q : FixedFiber.Coord) (i : Index) (hi : i.1 = baseChart c) :
    (homogeneousSection t f).coefficient i (FixedFiber.param t c e q) =
      f.value (t,baseVector c t (Blowup.projection (localParam e q))) := by
  change f.value (t,FailureOfSemipositiveMetricExtension.ProjectivePlane.vector i.1
    (FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates i.1
      (affineBase c t (Blowup.projection (localParam e q))))) = _
  rw [hi,affineBase_eq_param,FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates_param,baseVector_eq_vector]

/-- The four undivided cubic sections of the actual H³ bundle on any fixed fibre. -/
def cubicSections (t : ℂ) (k : Fin 4) : SectionData t 3 (fun _ => 0) :=
  homogeneousSection t (FailureOfSemipositiveMetricExtension.GlobalLineBundle.cubicGenerators k)

/-- In particular, the four actual H³ sections on the central compact complex surface. -/
def centralCubicSections (k : Fin 4) : SectionData 0 3 (fun _ => 0) := cubicSections 0 k

theorem cubicSections_contMDiff (t : ℂ) (k : Fin 4) :
    ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (sectionMap (cubicSections t k)) := sectionMap_contMDiff _

theorem centralCubicSections_contMDiff (k : Fin 4) :
    ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (sectionMap (centralCubicSections k)) := sectionMap_contMDiff _

@[simp] theorem cubicSections_projects (t : ℂ) (k : Fin 4) (p : Fiber t) :
    (core t 3 (fun _ => 0)).proj (sectionMap (cubicSections t k) p) = p := rfl

/-- The fixed-fibre section map really is the restriction of the global cubic section map. -/
theorem cubicSections_lift (t : ℂ) (k : Fin 4) (p : Fiber t) :
    bundleLift t 3 (fun _ => 0) (sectionMap (cubicSections t k) p) =
      FailureOfSemipositiveMetricExtension.GlobalLineBundle.sectionMap (FailureOfSemipositiveMetricExtension.GlobalLineBundle.cubicSections k)
        (FixedFiber.inclusion t p) := rfl

theorem cubicSections_coefficient (t : ℂ) (k : Fin 4) (i : Index) (p : Fiber t) :
    (cubicSections t k).coefficient i p =
      let v := FailureOfSemipositiveMetricExtension.ProjectivePlane.vector i.1
        (FailureOfSemipositiveMetricExtension.ProjectivePlane.coordinates i.1 (FixedFiber.blowdown t p))
      ![FailureOfSemipositiveMetricExtension.Cubics.g₁ (v 0) (v 1) (v 2),
        FailureOfSemipositiveMetricExtension.Cubics.g₂ (v 0) (v 1) (v 2),
        FailureOfSemipositiveMetricExtension.Cubics.g₃ (v 0) (v 1) (v 2),
        FailureOfSemipositiveMetricExtension.Cubics.g₄ (v 0) (v 1) (v 2)] k := rfl

/-- Exact compatibility with the earlier polynomial blow-up computations at t=0. -/
theorem centralCubicSections_coefficient_param (k : Fin 4) (c : Fin 4) (e : Fin 2)
    (q : FixedFiber.Coord) (i : Index) (hi : i.1 = baseChart c) :
    (centralCubicSections k).coefficient i (FixedFiber.param 0 c e q) =
      let v := baseVector c 0 (Blowup.projection (localParam e q))
      ![FailureOfSemipositiveMetricExtension.Cubics.g₁ (v 0) (v 1) (v 2),
        FailureOfSemipositiveMetricExtension.Cubics.g₂ (v 0) (v 1) (v 2),
        FailureOfSemipositiveMetricExtension.Cubics.g₃ (v 0) (v 1) (v 2),
        FailureOfSemipositiveMetricExtension.Cubics.g₄ (v 0) (v 1) (v 2)] k :=
  homogeneousSection_coefficient_param 0 (FailureOfSemipositiveMetricExtension.GlobalLineBundle.cubicGenerators k) c e q i hi

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
