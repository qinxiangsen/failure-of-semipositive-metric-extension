import FailureOfSemipositiveMetricExtension.CentralSmallStalkVanishing
import FailureOfSemipositiveMetricExtension.AdjointMapMultiplierGerms

/-! The first nonzero integrable central adjoint system is exactly m=4.
The small-system vanishing is for arbitrary actual adjoint-bundle section maps.
Multiplier germs, canonical-frame units, genuine local holomorphic division,
actual residual bundles, and projective-line geometry are all connected. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

theorem actual_central_first_adjoint_section_zero
    (s : ∀ p : Fiber 0, (adjointCore 0 1).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (fun p => (⟨p,s p⟩ : (adjointCore 0 1).TotalSpace))) (p : Fiber 0) : s p = 0 := by
  have hz := central_first_ambient_section_zero (ambientDataOfAdjointMap 0 1 s hs) p
  rw [ambientDataOfAdjointMap_value] at hz
  apply (adjointFiberEquiv 0 1 p).symm.injective
  rw [map_zero]
  exact hz

theorem actual_central_second_integrable_adjoint_section_zero
    (s : ∀ p : Fiber 0, (adjointCore 0 2).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (fun p => (⟨p,s p⟩ : (adjointCore 0 2).TotalSpace)))
    (hI : HasCentralIntegrableGerms 2 s hs) (p : Fiber 0) : s p = 0 := by
  have hg := (central_integrable_germs_iff_ambient_ellPower 2 s hs).mp hI
  have hz := central_second_ambient_stalk_section_zero (ambientDataOfAdjointMap 0 2 s hs) hg p
  rw [ambientDataOfAdjointMap_value] at hz
  apply (adjointFiberEquiv 0 2 p).symm.injective
  rw [map_zero]
  exact hz

theorem actual_central_third_integrable_adjoint_section_zero
    (s : ∀ p : Fiber 0, (adjointCore 0 3).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (fun p => (⟨p,s p⟩ : (adjointCore 0 3).TotalSpace)))
    (hI : HasCentralIntegrableGerms 3 s hs) (p : Fiber 0) : s p = 0 := by
  have hg := (central_integrable_germs_iff_ambient_ellPower 3 s hs).mp hI
  have hz := central_third_ambient_stalk_section_zero (ambientDataOfAdjointMap 0 3 s hs) hg p
  rw [ambientDataOfAdjointMap_value] at hz
  apply (adjointFiberEquiv 0 3 p).symm.injective
  rw [map_zero]
  exact hz

/-- All genuine central integrable adjoint sections vanish for 1 ≤ m ≤ 3. -/
theorem actual_central_small_integrable_adjoint_section_zero (m : ℕ) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
    (s : ∀ p : Fiber 0, (adjointCore 0 m).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (fun p => (⟨p,s p⟩ : (adjointCore 0 m).TotalSpace)))
    (hI : HasCentralIntegrableGerms m s hs) (p : Fiber 0) : s p = 0 := by
  interval_cases m
  · exact actual_central_first_adjoint_section_zero s hs p
  · exact actual_central_second_integrable_adjoint_section_zero s hs hI p
  · exact actual_central_third_integrable_adjoint_section_zero s hs hI p

/-- The previously constructed genuine adjoint sigma satisfies exactly the same
actual-germ integrability predicate used in the small-system vanishing theorem. -/
theorem sigmaAdjoint_hasCentralIntegrableGerms :
    HasCentralIntegrableGerms 4 sigmaAdjointValue sigmaAdjointMap_contMDiff := by
  intro d p hp
  have hg : adjointMapGerm 4 sigmaAdjointValue sigmaAdjointMap_contMDiff d p hp =
      sigmaAdjointGerm d p hp := by
    unfold adjointMapGerm sigmaAdjointGerm
    congr 1
    apply Subtype.ext
    funext q
    exact congrArg Prod.snd (sigmaAdjointMap_localTriv d q q.2)
  rw [hg]
  exact sigmaAdjointGerm_weighted_integrable d p hp

/-- A genuine nonzero analytic integrable central adjoint section exists at m=4. -/
theorem actual_central_fourth_integrable_adjoint_section_exists :
    ∃ (s : ∀ p : Fiber 0, (adjointCore 0 4).Fiber p)
      (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
        (fun p => (⟨p,s p⟩ : (adjointCore 0 4).TotalSpace))),
      HasCentralIntegrableGerms 4 s hs ∧ ∃ p, s p ≠ 0 :=
  ⟨sigmaAdjointValue,sigmaAdjointMap_contMDiff,sigmaAdjoint_hasCentralIntegrableGerms,sigmaAdjoint_nonzero⟩

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
