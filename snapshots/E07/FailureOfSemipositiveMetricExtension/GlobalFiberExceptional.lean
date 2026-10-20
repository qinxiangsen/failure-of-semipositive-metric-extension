import FailureOfSemipositiveMetricExtension.GlobalFiberSections
import FailureOfSemipositiveMetricExtension.GlobalFiberExceptionalDensity
import FailureOfSemipositiveMetricExtension.GlobalDivisionCover

/-! Actual exceptional sections and a verified common refinement of bundle frames
and two-dimensional fibre charts. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle
open scoped Manifold ContDiff

abbrev DivisionIndex := FailureOfSemipositiveMetricExtension.GlobalLineBundle.DivisionIndex
abbrev divisionFrame := FailureOfSemipositiveMetricExtension.GlobalLineBundle.divisionFrame

def divisionPatch (t : ℂ) (d : DivisionIndex) : Set (Fiber t) :=
  FixedFiber.inclusion t ⁻¹' FailureOfSemipositiveMetricExtension.GlobalLineBundle.divisionPatch d

theorem divisionPatch_isOpen (t : ℂ) (d : DivisionIndex) : IsOpen (divisionPatch t d) :=
  (FailureOfSemipositiveMetricExtension.GlobalLineBundle.divisionPatch_isOpen d).preimage (FixedFiber.inclusion_continuous t)

theorem divisionPatch_cover (t : ℂ) (p : Fiber t) : ∃ d, p ∈ divisionPatch t d :=
  FailureOfSemipositiveMetricExtension.GlobalLineBundle.divisionPatch_cover (FixedFiber.inclusion t p)

theorem divisionPatch_subset_frame (t : ℂ) (d : DivisionIndex) :
    divisionPatch t d ⊆ baseSet t (divisionFrame d) := fun _ hp => hp.2

theorem divisionPatch_subset_source (t : ℂ) (d : DivisionIndex) :
    divisionPatch t d ⊆ FixedFiber.source t d.1 d.2.1 := fun _ hp => hp.1

theorem divisionPatch_avoids_other_centres (t : ℂ) (d : DivisionIndex) (p : Fiber t)
    (hp : p ∈ divisionPatch t d) (j : Fin 4) (hj : j ≠ d.1) :
    FixedFiber.blowdown t p ≠ centre j t :=
  FailureOfSemipositiveMetricExtension.GlobalLineBundle.divisionPatch_avoids_other_centres d (FixedFiber.inclusion t p) hp j hj

def exceptionalCoefficient (t : ℂ) (r : Fin 4) (i : Index) (p : Fiber t) : ℂ :=
  FailureOfSemipositiveMetricExtension.GlobalLineBundle.exceptionalCoefficient r i (FixedFiber.inclusion t p)

def exceptionalSection (t : ℂ) (r : Fin 4) :
    SectionData t 1 (FailureOfSemipositiveMetricExtension.GlobalLineBundle.exceptionalDegree r) :=
  pullback t (FailureOfSemipositiveMetricExtension.GlobalLineBundle.exceptionalSection r)

theorem exceptionalCoefficient_contMDiffOn (t : ℂ) (r : Fin 4) (i : Index) :
    ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω (exceptionalCoefficient t r i) (baseSet t i) :=
  (exceptionalSection t r).analytic i

theorem exceptionalCoefficient_zero_iff (t : ℂ) (r : Fin 4) (i : Index) (p : Fiber t)
    (hp : p ∈ baseSet t i) :
    exceptionalCoefficient t r i p = 0 ↔ FixedFiber.blowdown t p = centre r t :=
  FailureOfSemipositiveMetricExtension.GlobalLineBundle.exceptionalCoefficient_zero_iff r i (FixedFiber.inclusion t p) hp

theorem exceptionalCoefficient_param (t : ℂ) (d : DivisionIndex) (q : FixedFiber.Coord) :
    exceptionalCoefficient t d.1 (divisionFrame d) (FixedFiber.param t d.1 d.2.1 q) = q.1 :=
  FailureOfSemipositiveMetricExtension.GlobalLineBundle.exceptionalCoefficient_chartParam d.1 d.2.1 _
    (FailureOfSemipositiveMetricExtension.GlobalLineBundle.divisionFrame_selected d) (q,t)

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
