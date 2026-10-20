import FailureOfSemipositiveMetricExtension.CentralSmallIntegrableAdjointVanishing

/-! The least positive exponent with a nonzero actual analytic central adjoint
section satisfying the genuine multiplier-germ condition is exactly four. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold Topology
open scoped Manifold ContDiff

/-- Nonzero actual sections of the actual canonical tensor power bundle, with
actual weighted holomorphic germs in every genuine local frame. -/
def NonzeroCentralIntegrableAdjointSystem (m : ℕ) : Prop :=
  ∃ (s : ∀ p : Fiber 0, (adjointCore 0 m).Fiber p)
    (hs : ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (fun p => (⟨p,s p⟩ : (adjointCore 0 m).TotalSpace))),
    HasCentralIntegrableGerms m s hs ∧ ∃ p, s p ≠ 0

/-- A precise least-exponent statement for the actual integrable adjoint systems. -/
theorem first_nonzero_central_integrable_adjoint_exponent :
    IsLeast {m : ℕ | 1 ≤ m ∧ NonzeroCentralIntegrableAdjointSystem m} 4 := by
  constructor
  · exact ⟨by decide,actual_central_fourth_integrable_adjoint_section_exists⟩
  · intro m hm
    by_contra h
    have hm3 : m ≤ 3 := by omega
    obtain ⟨s,hs,hI,p,hp⟩ := hm.2
    exact hp (actual_central_small_integrable_adjoint_section_zero m hm.1 hm3 s hs hI p)

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
