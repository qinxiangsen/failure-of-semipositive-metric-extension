import FailureOfSemipositiveMetricExtension.CentralTransverseLineBundleIsomorphism
import FailureOfSemipositiveMetricExtension.ProjectiveLineNegativeSections

/-! Actual analytic sections restrict through the verified bundle isomorphism.
Negative restricted degree forces their values on the entire transverse line to vanish. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.CentralLine
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

def restrictedSectionMap (c : Data) (a : ℤ) (b : Fin 4 → ℤ)
    (s : ∀ p : Fiber 0, (FixedFiberBundle.core 0 a b).Fiber p) : Direction → RestrictedTotal c a b :=
  fun d => ⟨d,s (param c d)⟩

theorem restrictedSectionMap_contMDiff (c : Data) (a : ℤ) (b : Fin 4 → ℤ)
    (s : ∀ p : Fiber 0, (FixedFiberBundle.core 0 a b).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (fun p => (⟨p,s p⟩ : (FixedFiberBundle.core 0 a b).TotalSpace))) :
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ω (restrictedSectionMap c a b s) := by
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
      (hs.contMDiffAt.comp d (param_contMDiff c ω).contMDiffAt)
    exact h.snd

/-- A genuine O(a+b₀+b₁+b₂) section, obtained by actual pullback and the actual
base-preserving bundle isomorphism. -/
def projectiveSection (c : Data) (a : ℤ) (b : Fin 4 → ℤ)
    (s : ∀ p : Fiber 0, (FixedFiberBundle.core 0 a b).Fiber p)
    (d : Direction) : (ProjectiveLineBundle.core (restrictionDegree a b)).Fiber d :=
  restrictionFiberEquiv c a b d (s (param c d))

theorem projectiveSection_contMDiff (c : Data) (a : ℤ) (b : Fin 4 → ℤ)
    (s : ∀ p : Fiber 0, (FixedFiberBundle.core 0 a b).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (fun p => (⟨p,s p⟩ : (FixedFiberBundle.core 0 a b).TotalSpace))) :
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ω
      (fun d => (⟨d,projectiveSection c a b s d⟩ : (ProjectiveLineBundle.core (restrictionDegree a b)).TotalSpace)) :=
  (restrictionBundleEquiv_contMDiff c a b).comp (restrictedSectionMap_contMDiff c a b s hs)

/-- Vanishing along every point of the actual parametrized transverse line. The only
section hypothesis is analyticity of the genuine total-space section map. -/
theorem negative_restriction_section_zero (c : Data) (a : ℤ) (b : Fin 4 → ℤ)
    (hdeg : restrictionDegree a b < 0)
    (s : ∀ p : Fiber 0, (FixedFiberBundle.core 0 a b).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (fun p => (⟨p,s p⟩ : (FixedFiberBundle.core 0 a b).TotalSpace)))
    (d : Direction) : s (param c d) = 0 := by
  apply (restrictionFiberEquiv c a b d).injective
  rw [map_zero]
  exact ProjectiveLineBundle.analytic_section_zero (restrictionDegree a b) hdeg
    (projectiveSection c a b s) (projectiveSection_contMDiff c a b s hs) d

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.CentralLine
