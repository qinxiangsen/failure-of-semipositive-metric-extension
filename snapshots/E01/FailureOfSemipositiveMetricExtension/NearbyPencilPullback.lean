import FailureOfSemipositiveMetricExtension.NearbyPencilMap
import Mathlib.Geometry.Manifold.VectorBundle.Pullback

/-! The actual mathlib pullback of the actual projective-line O(1) bundle along
the verified nearby pencil map, retaining its standard pullback topology. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil
noncomputable section
open Set Bundle IsManifold Topology
open FixedFiberBundle
open scoped Manifold ContDiff

/-- The proved analytic pencil, bundled for mathlib's actual pullback construction. -/
def analyticMap (t : ℂ) (ht : t ≠ 0) :
    C^ω⟮𝓘(ℂ,FixedFiber.Coord), Fiber t; 𝓘(ℂ), ProjectiveLine.Point⟯ :=
  ⟨pencilMap t,pencilMap_contMDiff t ht⟩

abbrev PullbackFiber (t : ℂ) (ht : t ≠ 0) :=
  (analyticMap t ht) *ᵖ (ProjectiveLineBundle.core 1).Fiber

abbrev PullbackTotal (t : ℂ) (ht : t ≠ 0) := TotalSpace ℂ (PullbackFiber t ht)

theorem pullback_analytic (t : ℂ) (ht : t ≠ 0) :
    ContMDiffVectorBundle ω ℂ (PullbackFiber t ht) 𝓘(ℂ,FixedFiber.Coord) := inferInstance

theorem pullback_finrank (t : ℂ) (ht : t ≠ 0) (p : Fiber t) :
    Module.finrank ℂ (PullbackFiber t ht p) = 1 := Module.finrank_self ℂ

def pullbackTriv (t : ℂ) (ht : t ≠ 0) (k : Fin 2) :
    Trivialization ℂ (π ℂ (PullbackFiber t ht)) :=
  ((ProjectiveLineBundle.core 1).localTriv k).pullback (analyticMap t ht)

instance pullbackTriv_mem_atlas (t : ℂ) (ht : t ≠ 0) (k : Fin 2) :
    MemTrivializationAtlas (pullbackTriv t ht k) := by
  haveI : MemTrivializationAtlas ((ProjectiveLineBundle.core 1).localTriv k) := ⟨⟨k,rfl⟩⟩
  exact ⟨⟨(ProjectiveLineBundle.core 1).localTriv k,inferInstance,rfl⟩⟩

@[simp] theorem pullbackTriv_baseSet (t : ℂ) (ht : t ≠ 0) (k : Fin 2) :
    (pullbackTriv t ht k).baseSet = pencilMap t ⁻¹' ProjectiveLine.chartSet k := rfl

/-- The standard pullback projection to O(1), with its original bundle topology. -/
def pullbackLift (t : ℂ) (ht : t ≠ 0) : PullbackTotal t ht → (ProjectiveLineBundle.core 1).TotalSpace :=
  Pullback.lift (analyticMap t ht)

@[simp] theorem pullbackLift_projects (t : ℂ) (ht : t ≠ 0) (z : PullbackTotal t ht) :
    (pullbackLift t ht z).proj = pencilMap t z.proj := rfl

@[simp] theorem pullbackTriv_apply (t : ℂ) (ht : t ≠ 0) (k : Fin 2) (z : PullbackTotal t ht) :
    pullbackTriv t ht k z =
      (z.proj,((ProjectiveLineBundle.core 1).localTriv k (pullbackLift t ht z)).2) := rfl

theorem pullbackLift_contMDiff (t : ℂ) (ht : t ≠ 0) :
    ContMDiff (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω (pullbackLift t ht) := by
  intro z
  let k := (ProjectiveLineBundle.core 1).indexAt (pencilMap t z.proj)
  have hp : pencilMap t z.proj ∈ ProjectiveLine.chartSet k :=
    (ProjectiveLineBundle.core 1).mem_baseSet_at _
  let eo := (ProjectiveLineBundle.core 1).localTriv k
  let ep := pullbackTriv t ht k
  haveI : MemTrivializationAtlas eo := ⟨⟨k,rfl⟩⟩
  apply (eo.contMDiffAt_iff (show pullbackLift t ht z ∈ eo.source from hp)).mpr
  constructor
  · exact (pencilMap_contMDiff t ht).contMDiffAt.comp z
      (Bundle.contMDiffAt_proj (PullbackFiber t ht))
  · have h : ContMDiffAt (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ))
        (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω ep z :=
      ep.contMDiffOn.contMDiffAt (ep.open_source.mem_nhds hp)
    exact h.snd

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.NearbyPencil
