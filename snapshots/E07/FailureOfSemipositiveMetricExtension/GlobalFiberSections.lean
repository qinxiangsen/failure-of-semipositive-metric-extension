import FailureOfSemipositiveMetricExtension.GlobalFiberLineBundle
import FailureOfSemipositiveMetricExtension.GlobalBundleSections

/-! Genuine analytic sections of the pulled-back fixed-fibre line bundles.
Global coherent section data restrict along the actual analytic fibre inclusion,
and the resulting section maps commute with the canonical bundle lift. -/

namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold
open scoped Manifold ContDiff Topology

structure SectionData (t : ℂ) (a : ℤ) (b : Fin 4 → ℤ) where
  coefficient : Index → Fiber t → ℂ
  analytic : ∀ i, ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω (coefficient i) (baseSet t i)
  compatible : ∀ i j p, p ∈ baseSet t i ∩ baseSet t j →
    gain t a b i j p * coefficient i p = coefficient j p

def sectionValue {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ} (s : SectionData t a b) (p : Fiber t) :
    (core t a b).Fiber p := s.coefficient ((core t a b).indexAt p) p

def sectionMap {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ} (s : SectionData t a b) :
    Fiber t → (core t a b).TotalSpace := fun p => ⟨p,sectionValue s p⟩

@[simp] theorem sectionMap_projects {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ}
    (s : SectionData t a b) (p : Fiber t) : (core t a b).proj (sectionMap s p) = p := rfl

theorem sectionMap_localTriv {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ} (s : SectionData t a b)
    (i : Index) (p : Fiber t) (hp : p ∈ baseSet t i) :
    (core t a b).localTriv i (sectionMap s p) = (p,s.coefficient i p) := by
  rw [VectorBundleCore.localTriv_apply]
  congr 1
  exact s.compatible ((core t a b).indexAt p) i p ⟨(core t a b).mem_baseSet_at p,hp⟩

theorem sectionMap_contMDiff {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ} (s : SectionData t a b) :
    ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω (sectionMap s) := by
  intro p
  let i := (core t a b).indexAt p
  have hp : p ∈ baseSet t i := (core t a b).mem_baseSet_at p
  let e := (core t a b).localTriv i
  haveI : MemTrivializationAtlas e := ⟨⟨i,rfl⟩⟩
  apply (e.contMDiffAt_iff (show sectionMap s p ∈ e.source from hp)).mpr
  refine ⟨contMDiffAt_id,?_⟩
  have hnb : baseSet t i ∈ 𝓝 p := (core t a b).isOpen_baseSet i |>.mem_nhds hp
  exact ((s.analytic i).congr (fun q hq =>
    congrArg Prod.snd (sectionMap_localTriv s i q hq))).contMDiffAt hnb

theorem sectionValue_zero_iff {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ} (s : SectionData t a b)
    (i : Index) (p : Fiber t) (hp : p ∈ baseSet t i) :
    sectionValue s p = 0 ↔ s.coefficient i p = 0 := by
  have hc := s.compatible ((core t a b).indexAt p) i p ⟨(core t a b).mem_baseSet_at p,hp⟩
  have hi := s.compatible i ((core t a b).indexAt p) p ⟨hp,(core t a b).mem_baseSet_at p⟩
  constructor
  · intro hz
    change s.coefficient ((core t a b).indexAt p) p = 0 at hz
    simpa [hz] using hc.symm
  · intro hz
    change s.coefficient ((core t a b).indexAt p) p = 0
    simpa [hz] using hi.symm

/-- Pull back actual global coherent analytic data to the actual fixed fibre. -/
def pullback (t : ℂ) {a : ℤ} {b : Fin 4 → ℤ}
    (s : FailureOfSemipositiveMetricExtension.GlobalLineBundle.SectionData a b) : SectionData t a b where
  coefficient i p := s.coefficient i (FixedFiber.inclusion t p)
  analytic i := (s.analytic i).comp (FixedFiber.inclusion_contMDiff t ω).contMDiffOn (fun _ hp => hp)
  compatible i j p hp := s.compatible i j (FixedFiber.inclusion t p) hp

@[simp] theorem pullback_coefficient (t : ℂ) {a : ℤ} {b : Fin 4 → ℤ}
    (s : FailureOfSemipositiveMetricExtension.GlobalLineBundle.SectionData a b) (i : Index) (p : Fiber t) :
    (pullback t s).coefficient i p = s.coefficient i (FixedFiber.inclusion t p) := rfl

/-- Pullback of coherent data agrees fibrewise with pullback of the genuine global section. -/
@[simp] theorem pullback_sectionValue (t : ℂ) {a : ℤ} {b : Fin 4 → ℤ}
    (s : FailureOfSemipositiveMetricExtension.GlobalLineBundle.SectionData a b) (p : Fiber t) :
    fiberEquiv t a b p (sectionValue (pullback t s) p) =
      FailureOfSemipositiveMetricExtension.GlobalLineBundle.sectionValue s (FixedFiber.inclusion t p) := rfl

/-- The square of actual section maps and canonical total-space lift commutes exactly. -/
@[simp] theorem bundleLift_pullback_sectionMap (t : ℂ) {a : ℤ} {b : Fin 4 → ℤ}
    (s : FailureOfSemipositiveMetricExtension.GlobalLineBundle.SectionData a b) (p : Fiber t) :
    bundleLift t a b (sectionMap (pullback t s) p) =
      FailureOfSemipositiveMetricExtension.GlobalLineBundle.sectionMap s (FixedFiber.inclusion t p) := rfl

theorem pullback_sectionMap_contMDiff (t : ℂ) {a : ℤ} {b : Fin 4 → ℤ}
    (s : FailureOfSemipositiveMetricExtension.GlobalLineBundle.SectionData a b) :
    ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (sectionMap (pullback t s)) := sectionMap_contMDiff _

/-- Pullback has precisely the inverse-image zero set of the original section. -/
theorem pullback_zero_iff (t : ℂ) {a : ℤ} {b : Fin 4 → ℤ}
    (s : FailureOfSemipositiveMetricExtension.GlobalLineBundle.SectionData a b) (p : Fiber t) :
    sectionValue (pullback t s) p = 0 ↔
      FailureOfSemipositiveMetricExtension.GlobalLineBundle.sectionValue s (FixedFiber.inclusion t p) = 0 := Iff.rfl

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
