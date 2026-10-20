import FailureOfSemipositiveMetricExtension.FixedFiberCanonicalTangentForms

/-! Coherent analytic sections of the actual canonical tensor L^m bundle,
retaining actual bundle topology, frame transitions, and zero values. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

structure AdjointSectionData (t : ℂ) (m : ℕ) where
  coefficient : DivisionIndex → Fiber t → ℂ
  analytic : ∀ d, ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω (coefficient d) (divisionPatch t d)
  compatible : ∀ d c p, p ∈ divisionPatch t d → p ∈ divisionPatch t c →
    adjointGain t m d c p * coefficient d p = coefficient c p

def adjointSectionValue {t : ℂ} {m : ℕ} (s : AdjointSectionData t m) (p : Fiber t) :
    (adjointCore t m).Fiber p := s.coefficient ((adjointCore t m).indexAt p) p

def adjointSectionMap {t : ℂ} {m : ℕ} (s : AdjointSectionData t m) :
    Fiber t → (adjointCore t m).TotalSpace := fun p => ⟨p,adjointSectionValue s p⟩

@[simp] theorem adjointSectionMap_projects {t : ℂ} {m : ℕ} (s : AdjointSectionData t m) (p : Fiber t) :
    (adjointSectionMap s p).proj = p := rfl

theorem adjointSectionMap_localTriv {t : ℂ} {m : ℕ} (s : AdjointSectionData t m)
    (d : DivisionIndex) (p : Fiber t) (hp : p ∈ divisionPatch t d) :
    (adjointCore t m).localTriv d (adjointSectionMap s p) = (p,s.coefficient d p) := by
  rw [VectorBundleCore.localTriv_apply]
  apply Prod.ext
  · rfl
  · exact s.compatible _ d p ((adjointCore t m).mem_baseSet_at p) hp

theorem adjointSectionMap_contMDiff {t : ℂ} {m : ℕ} (s : AdjointSectionData t m) :
    ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω (adjointSectionMap s) := by
  intro p
  let d := (adjointCore t m).indexAt p
  have hp : p ∈ divisionPatch t d := (adjointCore t m).mem_baseSet_at p
  let e := (adjointCore t m).localTriv d
  haveI : MemTrivializationAtlas e := ⟨⟨d,rfl⟩⟩
  apply (e.contMDiffAt_iff (show adjointSectionMap s p ∈ e.source from hp)).mpr
  refine ⟨contMDiffAt_id,?_⟩
  exact ((s.analytic d).congr (fun q hq =>
    congrArg Prod.snd (adjointSectionMap_localTriv s d q hq))).contMDiffAt
      ((divisionPatch_isOpen t d).mem_nhds hp)

theorem adjointSectionValue_zero_iff {t : ℂ} {m : ℕ} (s : AdjointSectionData t m)
    (d : DivisionIndex) (p : Fiber t) (hp : p ∈ divisionPatch t d) :
    adjointSectionValue s p = 0 ↔ s.coefficient d p = 0 := by
  have hc := s.compatible ((adjointCore t m).indexAt p) d p ((adjointCore t m).mem_baseSet_at p) hp
  have hi := s.compatible d ((adjointCore t m).indexAt p) p hp ((adjointCore t m).mem_baseSet_at p)
  constructor
  · intro hz
    change s.coefficient ((adjointCore t m).indexAt p) p = 0 at hz
    simpa [hz] using hc.symm
  · intro hz
    change s.coefficient ((adjointCore t m).indexAt p) p = 0
    simpa [hz] using hi.symm

def sigmaAdjointData : AdjointSectionData 0 4 where
  coefficient := sigmaAdjointCoefficient
  analytic := sigmaAdjointCoefficient_analytic
  compatible := sigmaAdjointCoefficient_compatible

@[simp] theorem sigmaAdjointData_value (p : Fiber 0) :
    adjointSectionValue sigmaAdjointData p = sigmaAdjointValue p := rfl

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
