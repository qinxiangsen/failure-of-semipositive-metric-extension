import FailureOfSemipositiveMetricExtension.GlobalAnalyticLineBundle

/-! Analytic local data glue to actual analytic sections of the global line bundles. -/
namespace FailureOfSemipositiveMetricExtension.GlobalLineBundle
noncomputable section
open Set Bundle IsManifold FailureOfSemipositiveMetricExtension.GlobalIncidence
open scoped Manifold ContDiff Topology

structure SectionData (a : ℤ) (b : Fin 4 → ℤ) where
  coefficient : Index → Total → ℂ
  analytic : ∀ i, ContMDiffOn 𝓘(ℂ,ChartCoord) 𝓘(ℂ) ω (coefficient i) (baseSet i)
  compatible : ∀ i j p, p ∈ baseSet i ∩ baseSet j →
    gain a b i j p * coefficient i p = coefficient j p

def sectionValue {a : ℤ} {b : Fin 4 → ℤ} (s : SectionData a b) (p : Total) :
    (core a b).Fiber p := s.coefficient ((core a b).indexAt p) p

def sectionMap {a : ℤ} {b : Fin 4 → ℤ} (s : SectionData a b) : Total → (core a b).TotalSpace :=
  fun p => ⟨p,sectionValue s p⟩

@[simp] theorem sectionMap_projects {a : ℤ} {b : Fin 4 → ℤ} (s : SectionData a b) (p : Total) :
    (core a b).proj (sectionMap s p) = p := rfl

theorem sectionMap_localTriv {a : ℤ} {b : Fin 4 → ℤ} (s : SectionData a b)
    (i : Index) (p : Total) (hp : p ∈ baseSet i) :
    (core a b).localTriv i (sectionMap s p) = (p,s.coefficient i p) := by
  rw [VectorBundleCore.localTriv_apply]
  congr 1
  exact s.compatible ((core a b).indexAt p) i p ⟨(core a b).mem_baseSet_at p,hp⟩

theorem sectionMap_contMDiff {a : ℤ} {b : Fin 4 → ℤ} (s : SectionData a b) :
    ContMDiff 𝓘(ℂ,ChartCoord) (𝓘(ℂ,ChartCoord).prod 𝓘(ℂ)) ω (sectionMap s) := by
  intro p
  let i := (core a b).indexAt p
  have hp : p ∈ baseSet i := (core a b).mem_baseSet_at p
  let e := (core a b).localTriv i
  haveI : MemTrivializationAtlas e := ⟨⟨i,rfl⟩⟩
  apply (e.contMDiffAt_iff (show sectionMap s p ∈ e.source from hp)).mpr
  refine ⟨contMDiffAt_id,?_⟩
  have hnb : baseSet i ∈ 𝓝 p := (core a b).isOpen_baseSet i |>.mem_nhds hp
  exact ((s.analytic i).congr (fun q hq =>
    congrArg Prod.snd (sectionMap_localTriv s i q hq))).contMDiffAt hnb

theorem sectionValue_zero_iff {a : ℤ} {b : Fin 4 → ℤ} (s : SectionData a b)
    (i : Index) (p : Total) (hp : p ∈ baseSet i) :
    sectionValue s p = 0 ↔ s.coefficient i p = 0 := by
  have hc := s.compatible ((core a b).indexAt p) i p ⟨(core a b).mem_baseSet_at p,hp⟩
  have hi := s.compatible i ((core a b).indexAt p) p ⟨hp,(core a b).mem_baseSet_at p⟩
  constructor
  · intro hz
    change s.coefficient ((core a b).indexAt p) p = 0 at hz
    simpa [hz] using hc.symm
  · intro hz
    change s.coefficient ((core a b).indexAt p) p = 0
    simpa [hz] using hi.symm
end
end FailureOfSemipositiveMetricExtension.GlobalLineBundle
