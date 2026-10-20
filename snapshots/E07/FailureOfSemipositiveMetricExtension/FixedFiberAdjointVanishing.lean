import FailureOfSemipositiveMetricExtension.FixedFiberAdjointIsomorphism
import FailureOfSemipositiveMetricExtension.NearbyAdjointVanishing

/-! Vanishing on every nearby actual surface of arbitrary actual analytic
sections of the genuine Jacobian-canonical tensor L^m bundle. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

/-- For every t ≠ 0 and every natural m, every genuine analytic section of
K_(X_t) tensor L_t^m is zero at every point. All geometric input is proved in
this development: the actual conic maps, actual bundle isomorphism, and density. -/
theorem actual_nearby_adjoint_section_zero (t : ℂ) (ht : t ≠ 0) (m : ℕ)
    (s : ∀ p : Fiber t, (adjointCore t m).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (fun p => (⟨p,s p⟩ : (adjointCore t m).TotalSpace)))
    (p : Fiber t) : s p = 0 := by
  let a : ∀ q : Fiber t, (ambientAdjointCore t m).Fiber q :=
    fun q => (adjointFiberEquiv t m q).symm (s q)
  have ha : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (fun q => (⟨q,a q⟩ : (ambientAdjointCore t m).TotalSpace)) :=
    (adjointBundleEquiv_symm_contMDiff t m).comp hs
  have hz := NearbyPencil.Conic.nearby_adjoint_section_zero t ht (m:ℤ) a ha p
  apply (adjointFiberEquiv t m p).symm.injective
  rw [map_zero]
  exact hz

/-- The actual new all-m equivalence sends the original sigma section to exactly
the already constructed canonical tensor L^4 section, without a new normalization. -/
theorem adjointBundleEquiv_sigma (p : Fiber 0) :
    adjointBundleEquiv 0 4 (sectionMap sigmaSection p) = sigmaAdjointMap p := by
  let d := canonicalPatchAt 0 p
  have hd := canonicalPatchAt_mem 0 p
  have hs := congrArg Prod.snd (sectionMap_localTriv sigmaSection (divisionFrame d) p hd.2)
  apply congrArg (fun v => (⟨p,v⟩ : (adjointCore 0 4).TotalSpace))
  change (canonicalFactor 0 d p *
    gain 0 (-7) (fun _ => 3) ((core 0 (-7) (fun _ => 3)).indexAt p) (divisionFrame d) p) *
      (show ℂ from sectionValue sigmaSection p) =
    canonicalFactor 0 d p * sigmaSection.coefficient (divisionFrame d) p
  rw [mul_assoc]
  exact congrArg (fun v : ℂ => canonicalFactor 0 d p * v) hs

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
