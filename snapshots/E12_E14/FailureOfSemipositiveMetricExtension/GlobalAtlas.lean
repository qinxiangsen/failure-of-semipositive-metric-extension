import FailureOfSemipositiveMetricExtension.GlobalChartTopology

/-! The actual eight-chart atlas on the already topologized global incidence space.
No topology is replaced: every chart is a partial homeomorphism for the ambient
subspace topology proved in `GlobalTopology`. -/

namespace FailureOfSemipositiveMetricExtension.GlobalIncidence
noncomputable section
open Set

/-- Every point lies in one of the eight genuine open chart sources. -/
theorem exists_homeomorphChart_source (p : Total) :
    ∃ k : Fin 4 × Fin 2, p ∈ (homeomorphChart k.1 k.2).source := by
  obtain ⟨i,e,q,hq,hp⟩ := global_charts_cover p
  exact ⟨(i,e),q,hq,hp.symm⟩

/-- A choice of one chart containing each point. -/
def chartIndex (p : Total) : Fin 4 × Fin 2 :=
  Classical.choose (exists_homeomorphChart_source p)

theorem chartIndex_mem_source (p : Total) :
    p ∈ (homeomorphChart (chartIndex p).1 (chartIndex p).2).source :=
  Classical.choose_spec (exists_homeomorphChart_source p)

/-- The genuine eight-chart structure on the incidence-subspace total space. -/
instance instChartedSpaceTotal : ChartedSpace ChartCoord Total where
  atlas := range (fun k : Fin 4 × Fin 2 => homeomorphChart k.1 k.2)
  chartAt p := homeomorphChart (chartIndex p).1 (chartIndex p).2
  mem_chart_source := chartIndex_mem_source
  chart_mem_atlas p := ⟨chartIndex p,rfl⟩

theorem mem_atlas_iff (c : PartialHomeomorph Total ChartCoord) :
    c ∈ atlas ChartCoord Total ↔ ∃ i e, c = homeomorphChart i e := by
  change (∃ k : Fin 4 × Fin 2, homeomorphChart k.1 k.2 = c) ↔ _
  constructor
  · rintro ⟨k,hk⟩
    exact ⟨k.1,k.2,hk.symm⟩
  · rintro ⟨i,e,rfl⟩
    exact ⟨(i,e),rfl⟩

theorem homeomorphChart_mem_atlas (i : Fin 4) (e : Fin 2) :
    homeomorphChart i e ∈ atlas ChartCoord Total :=
  (mem_atlas_iff _).mpr ⟨i,e,rfl⟩

/-- The exact domain of a change of global coordinates. -/
theorem transition_source (i j : Fin 4) (e f : Fin 2) :
    ((homeomorphChart i e).symm.trans (homeomorphChart j f)).source =
      chartDomain i e ∩ chartParam i e ⁻¹' chartSource j f := rfl

/-- Changes of coordinates equal the explicit normalized inverse formulas. -/
theorem transition_apply (i j : Fin 4) (e f : Fin 2) (q : ChartCoord)
    (hq : q ∈ ((homeomorphChart i e).symm.trans (homeomorphChart j f)).source) :
    ((homeomorphChart i e).symm.trans (homeomorphChart j f)) q =
      explicitCoordinates j f (chartParam i e q) :=
  chartCoordinates_eq_explicit j f _ hq.2

/-- The global topology instance remains precisely the original ambient-subspace instance. -/
theorem total_topology_instance_unchanged :
    (inferInstance : TopologicalSpace Total) = instTopologicalSpaceTotal := rfl

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence
