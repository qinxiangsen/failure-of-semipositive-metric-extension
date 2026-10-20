import FailureOfSemipositiveMetricExtension.HolomorphicStalks
import FailureOfSemipositiveMetricExtension.SingularHermitianWeights
import Mathlib.RingTheory.Ideal.Span

/-! Principal ideals of actual holomorphic stalks are independent of the bundle
frame. This constructs the divisor-ideal side of the eventual multiplier-ideal
identity; no integrability/divisibility equivalence is assumed. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold Manifold TopologicalSpace Opposite CategoryTheory
open scoped Manifold ContDiff

def coefficientSectionOn {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ} (s : SectionData t a b)
    (i : Index) (U : Opens (Fiber t)) (hU : (U : Set (Fiber t)) ⊆ baseSet t i) :
    C^∞⟮𝓘(ℂ,FixedFiber.Coord),U;𝓘(ℂ),ℂ⟯ :=
  ⟨fun p => s.coefficient i p,by
    intro p
    apply contMDiffAt_subtype_iff.mpr
    exact ((s.analytic i).of_le le_top).contMDiffAt ((baseSet_isOpen t i).mem_nhds (hU p.2))⟩

theorem sectionGerm_eq_restrict {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ} (s : SectionData t a b)
    (i : Index) (p : Fiber t) (hp : p ∈ baseSet t i)
    (U : Opens (Fiber t)) (hU : (U : Set (Fiber t)) ⊆ baseSet t i) (hpU : p ∈ U) :
    sectionGerm s i p hp = (holomorphicSheaf t).presheaf.germ U p hpU (coefficientSectionOn s i U hU) := by
  apply (holomorphicSheaf t).presheaf.germ_ext U hpU (homOfLE hU) (𝟙 U)
  apply Subtype.ext
  funext q
  rfl

def overlapOpen (t : ℂ) (i j : Index) : Opens (Fiber t) := frameOpen t i ⊓ frameOpen t j

def gainSection (t : ℂ) (a : ℤ) (b : Fin 4 → ℤ) (i j : Index) :
    C^∞⟮𝓘(ℂ,FixedFiber.Coord),overlapOpen t i j;𝓘(ℂ),ℂ⟯ :=
  ⟨fun p => gain t a b i j p,by
    intro p
    apply contMDiffAt_subtype_iff.mpr
    exact (gain_contMDiffOn t a b i j ∞).contMDiffAt
      (((baseSet_isOpen t i).inter (baseSet_isOpen t j)).mem_nhds p.2)⟩

def gainGerm (t : ℂ) (a : ℤ) (b : Fin 4 → ℤ) (i j : Index) (p : Fiber t)
    (hp : p ∈ baseSet t i ∩ baseSet t j) : HolomorphicStalk t p :=
  (holomorphicSheaf t).presheaf.germ (overlapOpen t i j) p hp (gainSection t a b i j)

theorem gainGerm_isUnit (t : ℂ) (a : ℤ) (b : Fin 4 → ℤ) (i j : Index) (p : Fiber t)
    (hp : p ∈ baseSet t i ∩ baseSet t j) : IsUnit (gainGerm t a b i j p hp) := by
  rw [smoothSheafCommRing.isUnit_stalk_iff,RingHom.mem_ker]
  change smoothSheafCommRing.eval 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) (Fiber t) ℂ p
    ((holomorphicSheaf t).presheaf.germ (overlapOpen t i j) p hp (gainSection t a b i j)) ≠ 0
  unfold holomorphicSheaf
  rw [smoothSheafCommRing.eval_germ]
  exact gain_ne_zero t a b i j p hp

/-- The precise transition identity in the actual holomorphic local ring. -/
theorem sectionGerm_transition {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ} (s : SectionData t a b)
    (i j : Index) (p : Fiber t) (hp : p ∈ baseSet t i ∩ baseSet t j) :
    gainGerm t a b i j p hp * sectionGerm s i p hp.1 = sectionGerm s j p hp.2 := by
  rw [sectionGerm_eq_restrict s i p hp.1 (overlapOpen t i j) (fun _ h => h.1) hp,
    sectionGerm_eq_restrict s j p hp.2 (overlapOpen t i j) (fun _ h => h.2) hp]
  unfold gainGerm
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  funext q
  exact s.compatible i j q q.2

/-- Powers of a local divisor equation generate the same ideal in all actual frames. -/
theorem sectionGerm_power_ideal_frame_independent {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ}
    (s : SectionData t a b) (k : ℕ) (i j : Index) (p : Fiber t)
    (hp : p ∈ baseSet t i ∩ baseSet t j) :
    Ideal.span ({(sectionGerm s i p hp.1)^k} : Set (HolomorphicStalk t p)) =
      Ideal.span ({(sectionGerm s j p hp.2)^k} : Set (HolomorphicStalk t p)) := by
  rw [← sectionGerm_transition s i j p hp,mul_pow,
    Ideal.span_singleton_mul_left_unit ((gainGerm_isUnit t a b i j p hp).pow k)]

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
