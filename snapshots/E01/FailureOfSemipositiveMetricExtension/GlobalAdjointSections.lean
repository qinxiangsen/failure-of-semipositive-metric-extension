import FailureOfSemipositiveMetricExtension.GlobalAdjointBundle
import FailureOfSemipositiveMetricExtension.FamilyNeighbourhoods

/-! Actual analytic adjoint sections on arbitrary open neighbourhoods, and their
restriction by the verified dt coefficient identity to whole nearby fibres. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalAdjoint
noncomputable section
open Set Bundle IsManifold Topology TopologicalSpace
open scoped Manifold ContDiff

structure SectionOn (U : Opens Total) (m : ℕ) where
  coefficient : Index → Total → ℂ
  analytic : ∀ d, ContMDiffOn 𝓘(ℂ,ChartCoord) 𝓘(ℂ) ω (coefficient d) (patch d ∩ U)
  compatible : ∀ d c p, p ∈ U → p ∈ patch d → p ∈ patch c →
    gain m d c p * coefficient d p = coefficient c p

def sectionValue {U : Opens Total} {m : ℕ} (s : SectionOn U m) (p : Total) :
    (core m).Fiber p := s.coefficient ((core m).indexAt p) p

def sectionMap {U : Opens Total} {m : ℕ} (s : SectionOn U m) : Total → (core m).TotalSpace :=
  fun p => ⟨p,sectionValue s p⟩

theorem sectionMap_localTriv {U : Opens Total} {m : ℕ} (s : SectionOn U m)
    (d : Index) (p : Total) (hp : p ∈ U) (hd : p ∈ patch d) :
    (core m).localTriv d (sectionMap s p) = (p,s.coefficient d p) := by
  rw [VectorBundleCore.localTriv_apply]
  apply Prod.ext
  · rfl
  · exact s.compatible _ d p hp ((core m).mem_baseSet_at p) hd

theorem sectionMap_contMDiffOn {U : Opens Total} {m : ℕ} (s : SectionOn U m) :
    ContMDiffOn 𝓘(ℂ,ChartCoord) (𝓘(ℂ,ChartCoord).prod 𝓘(ℂ)) ω (sectionMap s) U := by
  intro p hp
  let d := (core m).indexAt p
  have hd : p ∈ patch d := (core m).mem_baseSet_at p
  let e := (core m).localTriv d
  haveI : MemTrivializationAtlas e := ⟨⟨d,rfl⟩⟩
  apply ContMDiffAt.contMDiffWithinAt
  apply (e.contMDiffAt_iff (show sectionMap s p ∈ e.source from hd)).mpr
  refine ⟨contMDiffAt_id,?_⟩
  have hnb := ((GlobalLineBundle.divisionPatch_isOpen d).inter U.isOpen).mem_nhds ⟨hd,hp⟩
  exact ((s.analytic d).congr (fun q hq =>
    congrArg Prod.snd (sectionMap_localTriv s d q hq.2 hq.1))).contMDiffAt hnb

theorem sectionValue_zero_iff {U : Opens Total} {m : ℕ} (s : SectionOn U m)
    (d : Index) (p : Total) (hp : p ∈ U) (hd : p ∈ patch d) :
    sectionValue s p = 0 ↔ s.coefficient d p = 0 := by
  have hc := s.compatible ((core m).indexAt p) d p hp ((core m).mem_baseSet_at p) hd
  have hi := s.compatible d ((core m).indexAt p) p hp hd ((core m).mem_baseSet_at p)
  constructor
  · intro hz
    change s.coefficient ((core m).indexAt p) p = 0 at hz
    simpa [hz] using hc.symm
  · intro hz
    change s.coefficient ((core m).indexAt p) p = 0
    simpa [hz] using hi.symm

/-- Restriction to a whole actual fibre. Its frame coefficient identity is the
verified dt-adjunction identity, with the same actual L frame on each side. -/
def restriction {U : Opens Total} {m : ℕ} (s : SectionOn U m) (t : ℂ)
    (hU : ∀ p : Fiber t, FixedFiber.inclusion t p ∈ U) : FixedFiberBundle.AdjointSectionData t m where
  coefficient d p := s.coefficient d (FixedFiber.inclusion t p)
  analytic d := (s.analytic d).comp (FixedFiber.inclusion_contMDiff t ω).contMDiffOn
    (fun p hp => ⟨hp,hU p⟩)
  compatible d c p hd hc := by
    rw [← gain_inclusion t m d c p hd hc]
    exact s.compatible d c (FixedFiber.inclusion t p) (hU p) hd hc

@[simp] theorem restriction_coefficient {U : Opens Total} {m : ℕ} (s : SectionOn U m) (t : ℂ)
    (hU : ∀ p : Fiber t, FixedFiber.inclusion t p ∈ U) (d : Index) (p : Fiber t) :
    (restriction s t hU).coefficient d p = s.coefficient d (FixedFiber.inclusion t p) := rfl

/-- Equality of the actual local coordinates, not an assumed restriction map. -/
theorem restriction_localTriv {U : Opens Total} {m : ℕ} (s : SectionOn U m) (t : ℂ)
    (hU : ∀ p : Fiber t, FixedFiber.inclusion t p ∈ U) (d : Index) (p : Fiber t)
    (hd : p ∈ FixedFiberBundle.divisionPatch t d) :
    ((FixedFiberBundle.adjointCore t m).localTriv d
      (FixedFiberBundle.adjointSectionMap (restriction s t hU) p)).2 =
      ((core m).localTriv d (sectionMap s (FixedFiber.inclusion t p))).2 := by
  rw [FixedFiberBundle.adjointSectionMap_localTriv _ d p hd,
    sectionMap_localTriv s d (FixedFiber.inclusion t p) (hU p) hd]
  rfl

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalAdjoint
