import FailureOfSemipositiveMetricExtension.CentralCurveDegreeBundles
import FailureOfSemipositiveMetricExtension.ProjectiveLineNegativeSections

/-! Restriction of arbitrary actual analytic surface sections along the actual
central negative curve, through its standard pullback bundle isomorphism. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.CurvePullback
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

def restrictedSectionMap (a : ℤ) (b : Fin 4 → ℤ)
    (s : ∀ p : Fiber 0, (core 0 a b).Fiber p) : Direction → PullbackTotal a b :=
  fun d => ⟨d,s (lineParam d)⟩

theorem restrictedSectionMap_contMDiff (a : ℤ) (b : Fin 4 → ℤ)
    (s : ∀ p : Fiber 0, (core 0 a b).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (fun p => (⟨p,s p⟩ : (core 0 a b).TotalSpace))) :
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ω (restrictedSectionMap a b s) := by
  intro d
  let i := (ProjectiveLineBundle.core 0).indexAt d
  have hd : d ∈ ProjectiveLine.chartSet i := (ProjectiveLineBundle.core 0).mem_baseSet_at d
  have hi : lineParam d ∈ baseSet 0 (restrictionFrame i) :=
    (Set.ext_iff.mp (restrictionFrame_baseSet i) d).mpr hd
  let er := pullbackTriv a b i
  let ea := (core 0 a b).localTriv (restrictionFrame i)
  haveI : MemTrivializationAtlas ea := ⟨⟨restrictionFrame i,rfl⟩⟩
  apply (er.contMDiffAt_iff (show restrictedSectionMap a b s d ∈ er.source from hi)).mpr
  constructor
  · exact contMDiffAt_id
  · have h := (ea.contMDiffOn.contMDiffAt (ea.open_source.mem_nhds hi)).comp d
      (hs.contMDiffAt.comp d (lineParam_contMDiff ω).contMDiffAt)
    exact h.snd

def projectiveSection (a : ℤ) (b : Fin 4 → ℤ)
    (s : ∀ p : Fiber 0, (core 0 a b).Fiber p)
    (d : Direction) : (ProjectiveLineBundle.core (a+b 3)).Fiber d :=
  degreeFiberEquiv a b d (s (lineParam d))

theorem projectiveSection_contMDiff (a : ℤ) (b : Fin 4 → ℤ)
    (s : ∀ p : Fiber 0, (core 0 a b).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (fun p => (⟨p,s p⟩ : (core 0 a b).TotalSpace))) :
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ω
      (fun d => (⟨d,projectiveSection a b s d⟩ : (ProjectiveLineBundle.core (a+b 3)).TotalSpace)) :=
  (degreeHomeomorph_contMDiff a b).comp (restrictedSectionMap_contMDiff a b s hs)

theorem negative_restriction_section_zero (a : ℤ) (b : Fin 4 → ℤ) (hdeg : a+b 3 < 0)
    (s : ∀ p : Fiber 0, (core 0 a b).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (fun p => (⟨p,s p⟩ : (core 0 a b).TotalSpace))) (d : Direction) :
    s (lineParam d) = 0 := by
  apply (degreeFiberEquiv a b d).injective
  rw [map_zero]
  exact ProjectiveLineBundle.analytic_section_zero (a+b 3) hdeg
    (projectiveSection a b s) (projectiveSection_contMDiff a b s hs) d

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.CurvePullback
