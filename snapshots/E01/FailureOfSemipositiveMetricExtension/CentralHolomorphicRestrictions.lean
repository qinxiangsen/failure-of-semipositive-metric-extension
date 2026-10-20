import FailureOfSemipositiveMetricExtension.CentralResidualThreeVanishing
import FailureOfSemipositiveMetricExtension.ProjectiveLineHolomorphicSections

/-! Genuine restriction of complex C-infinity sections using the actual analytic
bundle isomorphisms. The one-dimensional Cauchy bridge supplies all analyticity
needed for projective-line vanishing. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.CentralLine.Holomorphic
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

def restrictedSectionMap (c : Data) (a : ℤ) (b : Fin 4 → ℤ)
    (s : ∀ p : Fiber 0, (FixedFiberBundle.core 0 a b).Fiber p) : Direction → RestrictedTotal c a b :=
  fun d => ⟨d,s (param c d)⟩

theorem restrictedSectionMap_contMDiff (c : Data) (a : ℤ) (b : Fin 4 → ℤ)
    (s : ∀ p : Fiber 0, (FixedFiberBundle.core 0 a b).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ∞
      (fun p => (⟨p,s p⟩ : (FixedFiberBundle.core 0 a b).TotalSpace))) :
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ∞ (restrictedSectionMap c a b s) := by
  intro d
  let i := selectedAmbientFrame c a b d
  have hi : param c d ∈ FixedFiberBundle.baseSet 0 i :=
    (FixedFiberBundle.core 0 a b).mem_baseSet_at _
  let er := restrictedTriv c a b i
  let ea := (FixedFiberBundle.core 0 a b).localTriv i
  haveI : MemTrivializationAtlas ea := ⟨⟨i,rfl⟩⟩
  apply (er.contMDiffAt_iff (show restrictedSectionMap c a b s d ∈ er.source from hi)).mpr
  constructor
  · exact contMDiffAt_id
  · have h := (ea.contMDiffOn.contMDiffAt (ea.open_source.mem_nhds hi)).comp d
      (hs.contMDiffAt.comp d (param_contMDiff c ∞).contMDiffAt)
    exact h.snd

/-- A genuine O(a+b₀+b₁+b₂) section, obtained by actual pullback and the actual
base-preserving bundle isomorphism. -/
def projectiveSection (c : Data) (a : ℤ) (b : Fin 4 → ℤ)
    (s : ∀ p : Fiber 0, (FixedFiberBundle.core 0 a b).Fiber p)
    (d : Direction) : (ProjectiveLineBundle.core (restrictionDegree a b)).Fiber d :=
  restrictionFiberEquiv c a b d (s (param c d))

theorem projectiveSection_contMDiff (c : Data) (a : ℤ) (b : Fin 4 → ℤ)
    (s : ∀ p : Fiber 0, (FixedFiberBundle.core 0 a b).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ∞
      (fun p => (⟨p,s p⟩ : (FixedFiberBundle.core 0 a b).TotalSpace))) :
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ∞
      (fun d => (⟨d,projectiveSection c a b s d⟩ : (ProjectiveLineBundle.core (restrictionDegree a b)).TotalSpace)) :=
  ((restrictionBundleEquiv_contMDiff c a b).of_le le_top).comp (restrictedSectionMap_contMDiff c a b s hs)

/-- Vanishing along every point of the actual parametrized transverse line. The only
section hypothesis is analyticity of the genuine total-space section map. -/
theorem negative_restriction_section_zero (c : Data) (a : ℤ) (b : Fin 4 → ℤ)
    (hdeg : restrictionDegree a b < 0)
    (s : ∀ p : Fiber 0, (FixedFiberBundle.core 0 a b).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ∞
      (fun p => (⟨p,s p⟩ : (FixedFiberBundle.core 0 a b).TotalSpace)))
    (d : Direction) : s (param c d) = 0 := by
  apply (restrictionFiberEquiv c a b d).injective
  rw [map_zero]
  exact ProjectiveLineBundle.holomorphic_section_zero (restrictionDegree a b) hdeg
    (projectiveSection c a b s) (projectiveSection_contMDiff c a b s hs) d

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.CentralLine.Holomorphic

namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.CurvePullback.Holomorphic
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

def restrictedSectionMap (a : ℤ) (b : Fin 4 → ℤ)
    (s : ∀ p : Fiber 0, (core 0 a b).Fiber p) : Direction → PullbackTotal a b :=
  fun d => ⟨d,s (lineParam d)⟩

theorem restrictedSectionMap_contMDiff (a : ℤ) (b : Fin 4 → ℤ)
    (s : ∀ p : Fiber 0, (core 0 a b).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ∞
      (fun p => (⟨p,s p⟩ : (core 0 a b).TotalSpace))) :
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ∞ (restrictedSectionMap a b s) := by
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
      (hs.contMDiffAt.comp d (lineParam_contMDiff ∞).contMDiffAt)
    exact h.snd

def projectiveSection (a : ℤ) (b : Fin 4 → ℤ)
    (s : ∀ p : Fiber 0, (core 0 a b).Fiber p)
    (d : Direction) : (ProjectiveLineBundle.core (a+b 3)).Fiber d :=
  degreeFiberEquiv a b d (s (lineParam d))

theorem projectiveSection_contMDiff (a : ℤ) (b : Fin 4 → ℤ)
    (s : ∀ p : Fiber 0, (core 0 a b).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ∞
      (fun p => (⟨p,s p⟩ : (core 0 a b).TotalSpace))) :
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ∞
      (fun d => (⟨d,projectiveSection a b s d⟩ : (ProjectiveLineBundle.core (a+b 3)).TotalSpace)) :=
  ((degreeHomeomorph_contMDiff a b).of_le le_top).comp (restrictedSectionMap_contMDiff a b s hs)

theorem negative_restriction_section_zero (a : ℤ) (b : Fin 4 → ℤ) (hdeg : a+b 3 < 0)
    (s : ∀ p : Fiber 0, (core 0 a b).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ∞
      (fun p => (⟨p,s p⟩ : (core 0 a b).TotalSpace))) (d : Direction) :
    s (lineParam d) = 0 := by
  apply (degreeFiberEquiv a b d).injective
  rw [map_zero]
  exact ProjectiveLineBundle.holomorphic_section_zero (a+b 3) hdeg
    (projectiveSection a b s) (projectiveSection_contMDiff a b s hs) d

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.CurvePullback.Holomorphic
