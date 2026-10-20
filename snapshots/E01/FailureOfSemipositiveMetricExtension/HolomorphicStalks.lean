import FailureOfSemipositiveMetricExtension.CentralAuxiliaryZeroSets
import Mathlib.Geometry.Manifold.Sheaf.LocallyRingedSpace

/-! Genuine complex-holomorphic structure sheaves and local rings on the actual
fibres. Here mathlib's complex C∞ sheaf is used, not the real smooth-function sheaf.
Every previously constructed analytic bundle coefficient defines an actual stalk germ. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold Manifold TopologicalSpace Opposite
open scoped Manifold ContDiff

def holomorphicSheaf (t : ℂ) :=
  smoothSheafCommRing 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) (Fiber t) ℂ

def holomorphicLocallyRingedSpace (t : ℂ) : AlgebraicGeometry.LocallyRingedSpace :=
  IsManifold.locallyRingedSpace 𝓘(ℂ,FixedFiber.Coord) (Fiber t)

abbrev HolomorphicStalk (t : ℂ) (p : Fiber t) := (holomorphicSheaf t).presheaf.stalk p

instance holomorphicStalk_isLocalRing (t : ℂ) (p : Fiber t) : IsLocalRing (HolomorphicStalk t p) :=
  smoothSheafCommRing.instLocalRing_stalk 𝓘(ℂ,FixedFiber.Coord) p

def frameOpen (t : ℂ) (i : Index) : Opens (Fiber t) := ⟨baseSet t i,baseSet_isOpen t i⟩

def coefficientSection {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ} (s : SectionData t a b) (i : Index) :
    C^∞⟮𝓘(ℂ,FixedFiber.Coord),frameOpen t i;𝓘(ℂ),ℂ⟯ :=
  ⟨fun p => s.coefficient i p,by
    intro p
    apply contMDiffAt_subtype_iff.mpr
    exact ((s.analytic i).of_le le_top).contMDiffAt ((baseSet_isOpen t i).mem_nhds p.2)⟩

def sectionGerm {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ} (s : SectionData t a b)
    (i : Index) (p : Fiber t) (hp : p ∈ baseSet t i) : HolomorphicStalk t p :=
  (holomorphicSheaf t).presheaf.germ (frameOpen t i) p hp (coefficientSection s i)

theorem sectionGerm_eval {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ} (s : SectionData t a b)
    (i : Index) (p : Fiber t) (hp : p ∈ baseSet t i) :
    smoothSheafCommRing.eval 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) (Fiber t) ℂ p (sectionGerm s i p hp) =
      s.coefficient i p := by
  exact smoothSheafCommRing.eval_germ (frameOpen t i) p hp (coefficientSection s i)

/-- A germ of a bundle coefficient is a unit precisely off the actual zero set. -/
theorem sectionGerm_isUnit_iff {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ} (s : SectionData t a b)
    (i : Index) (p : Fiber t) (hp : p ∈ baseSet t i) :
    IsUnit (sectionGerm s i p hp) ↔ sectionValue s p ≠ 0 := by
  rw [smoothSheafCommRing.isUnit_stalk_iff,RingHom.mem_ker,sectionGerm_eval]
  exact not_congr (sectionValue_zero_iff s i p hp).symm

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
