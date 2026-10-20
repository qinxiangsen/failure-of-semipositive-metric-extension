import FailureOfSemipositiveMetricExtension.GlobalAdjointSections

/-! Every genuine analytic section of the actual global adjoint bundle has the
coherent local coefficients used in the nonextension theorem. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalAdjoint
noncomputable section
open Set Bundle IsManifold Topology TopologicalSpace
open scoped Manifold ContDiff

/-- Extract coefficients from an arbitrary actual fibre-valued section whose
actual total-space map is analytic on the specified open set. -/
def ofAnalyticSection (U : Opens Total) (m : ℕ)
    (s : ∀ p : Total, (core m).Fiber p)
    (hs : ContMDiffOn 𝓘(ℂ,ChartCoord) (𝓘(ℂ,ChartCoord).prod 𝓘(ℂ)) ω
      (fun p => (⟨p,s p⟩ : (core m).TotalSpace)) U) : SectionOn U m where
  coefficient d p := ((core m).localTriv d ⟨p,s p⟩).2
  analytic d := by
    let e := (core m).localTriv d
    haveI : MemTrivializationAtlas e := ⟨⟨d,rfl⟩⟩
    have he := e.contMDiffOn.comp (hs.mono inter_subset_right)
      (show MapsTo (fun p => (⟨p,s p⟩ : (core m).TotalSpace)) (patch d ∩ U) e.source from fun _ hp => hp.1)
    exact contMDiff_snd.comp_contMDiffOn he
  compatible d c p hp hd hc := by
    change gain m d c p * (gain m ((core m).indexAt p) d p * (show ℂ from s p)) =
      gain m ((core m).indexAt p) c p * (show ℂ from s p)
    exact (core m).coordChange_comp ((core m).indexAt p) d c p
      ⟨⟨(core m).mem_baseSet_at p,hd⟩,hc⟩ (show ℂ from s p)

@[simp] theorem ofAnalyticSection_value (U : Opens Total) (m : ℕ)
    (s : ∀ p : Total, (core m).Fiber p)
    (hs : ContMDiffOn 𝓘(ℂ,ChartCoord) (𝓘(ℂ,ChartCoord).prod 𝓘(ℂ)) ω
      (fun p => (⟨p,s p⟩ : (core m).TotalSpace)) U) (p : Total) :
    sectionValue (ofAnalyticSection U m s hs) p = s p := by
  change gain m ((core m).indexAt p) ((core m).indexAt p) p * (show ℂ from s p) = s p
  simp [gain,GlobalLineBundle.gain_self]

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.GlobalAdjoint
