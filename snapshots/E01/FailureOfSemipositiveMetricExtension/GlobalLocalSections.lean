import FailureOfSemipositiveMetricExtension.GlobalAnalyticMaps

/-! Local analytic sections of the actual proper family projection. The global
extensions below need be regular only near their distinguished parameter;
there the chart domain gives their fully verified analyticity. -/

namespace FailureOfSemipositiveMetricExtension.GlobalIncidence
noncomputable section
open Set Topology
open scoped Manifold ContDiff

/-- The family map is exactly the last coordinate in all eight charts. -/
@[simp] theorem projection_chartParam (i : Fin 4) (e : Fin 2) (q : ChartCoord) :
    projection (chartParam i e q) = q.2 := rfl

/-- Through every point there is a section analytic near its parameter value. -/
theorem projection_local_analytic_section (p : Total) (n : WithTop ℕ∞) :
    ∃ s : ℂ → Total, s (projection p) = p ∧
      Function.RightInverse s projection ∧
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ,ChartCoord) n s (projection p) := by
  obtain ⟨i,e,q,hq,hp⟩ := global_charts_cover p
  let s : ℂ → Total := fun t => chartParam i e (q.1,t)
  have ht : projection p = q.2 := by rw [hp]; rfl
  have hs : s (projection p) = p := by
    dsimp [s]
    rw [ht]
    exact hp.symm
  refine ⟨s,hs,fun t => rfl,?_⟩
  have hc : ContMDiffAt 𝓘(ℂ,ChartCoord) 𝓘(ℂ,ChartCoord) n (chartParam i e) q :=
    (chartParam_contMDiffOn i e n).contMDiffAt ((chartDomain_isOpen i e).mem_nhds hq)
  have hv : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ,ChartCoord) n (fun t : ℂ => (q.1,t)) (projection p) :=
    (contDiff_const.prodMk contDiff_id).contMDiff.contMDiffAt
  have heq : (q.1,projection p) = q := by rw [ht]
  exact hc.comp_of_eq hv heq

/-- Analytic local sections imply the global proper family map is open. -/
theorem projection_isOpenMap : IsOpenMap projection := by
  apply IsOpenMap.of_sections
  intro p
  obtain ⟨s,hs,hsec,hreg⟩ := projection_local_analytic_section p 0
  exact ⟨s,by simpa only [hs] using hreg.continuousAt,hs,hsec⟩

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence
