import FailureOfSemipositiveMetricExtension.GlobalAdjointContinuation
import FailureOfSemipositiveMetricExtension.GlobalAdjointSectionCoordinates
import FailureOfSemipositiveMetricExtension.FixedFiberAdjointVanishing

/-! Unconditional nonextension of the actual nonzero central adjoint section.
This is the section obstruction in the paper; metric nonextension still requires
a correctly instantiated analytic extension theorem, not assumed here. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalAdjoint
noncomputable section
open Set Bundle IsManifold Topology TopologicalSpace
open scoped Manifold ContDiff

/-- Every actual neighbourhood adjoint section has zero dt-restriction to the
whole central fibre, for every m. The nearby vanishing input is fully proved. -/
theorem actual_central_restriction_zero {U : Opens Total} {m : ℕ}
    (s : SectionOn U m) (hU : ∀ p : Fiber 0, FixedFiber.inclusion 0 p ∈ U)
    (d : Index) (p : Fiber 0) (hd : p ∈ FixedFiberBundle.divisionPatch 0 d) :
    s.coefficient d (FixedFiber.inclusion 0 p) = 0 := by
  apply central_coefficient_zero_of_nearby_vanishing s hU _ d p hd
  intro t ht v q
  exact FixedFiberBundle.actual_nearby_adjoint_section_zero t ht m
    (FixedFiberBundle.adjointSectionValue v) (FixedFiberBundle.adjointSectionMap_contMDiff v) q

/-- The actual sigma in K_X0 tensor L_0^4 does not extend, under genuine
 dt-adjunction, to any open neighbourhood of the entire central fibre. -/
theorem sigma_adjoint_has_no_neighbourhood_extension (U : Opens Total)
    (hU : ∀ p : Fiber 0, FixedFiber.inclusion 0 p ∈ U) :
    ¬ ∃ s : SectionOn U 4, ∀ d p, p ∈ FixedFiberBundle.divisionPatch 0 d →
      s.coefficient d (FixedFiber.inclusion 0 p) = FixedFiberBundle.sigmaAdjointCoefficient d p := by
  apply no_extension_of_nearby_vanishing hU
  intro t ht v p
  exact FixedFiberBundle.actual_nearby_adjoint_section_zero t ht 4
    (FixedFiberBundle.adjointSectionValue v) (FixedFiberBundle.adjointSectionMap_contMDiff v) p

/-- The obstruction also applies directly to arbitrary genuine fibre-valued
analytic sections, rather than only a chosen coefficient representation. -/
theorem actual_sigma_section_has_no_neighbourhood_extension (U : Opens Total)
    (hU : ∀ p : Fiber 0, FixedFiber.inclusion 0 p ∈ U) :
    ¬ ∃ s : ∀ q : Total, (core 4).Fiber q,
      ContMDiffOn 𝓘(ℂ,ChartCoord) (𝓘(ℂ,ChartCoord).prod 𝓘(ℂ)) ω
        (fun q => (⟨q,s q⟩ : (core 4).TotalSpace)) U ∧
      ∀ d p, p ∈ FixedFiberBundle.divisionPatch 0 d →
        ((core 4).localTriv d ⟨FixedFiber.inclusion 0 p,s (FixedFiber.inclusion 0 p)⟩).2 =
          FixedFiberBundle.sigmaAdjointCoefficient d p := by
  rintro ⟨s,hs,he⟩
  exact sigma_adjoint_has_no_neighbourhood_extension U hU ⟨ofAnalyticSection U 4 s hs,he⟩

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalAdjoint
