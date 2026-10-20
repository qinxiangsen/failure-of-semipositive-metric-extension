import FailureOfSemipositiveMetricExtension.GlobalManifold

/-! Analyticity of the actual global structural maps. These maps are defined on
the constructed global manifold, with no smoothness assumptions added. -/

namespace FailureOfSemipositiveMetricExtension.GlobalIncidence
noncomputable section
open Set Topology IsManifold
open scoped Manifold ContDiff

/-- The verified global chart inverses are analytic on their actual open domains. -/
theorem chartParam_contMDiffOn (i : Fin 4) (e : Fin 2) (n : WithTop ℕ∞) :
    ContMDiffOn 𝓘(ℂ,ChartCoord) 𝓘(ℂ,ChartCoord) n (chartParam i e) (chartDomain i e) :=
  contMDiffOn_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (homeomorphChart_mem_atlas i e))

theorem chartCoordinates_contMDiffOn (i : Fin 4) (e : Fin 2) (n : WithTop ℕ∞) :
    ContMDiffOn 𝓘(ℂ,ChartCoord) 𝓘(ℂ,ChartCoord) n (chartCoordinates i e) (chartSource i e) :=
  contMDiffOn_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (homeomorphChart_mem_atlas i e))

/-- Analyticity can be checked on the eight actual parametrizations. -/
theorem contMDiff_of_chartParam {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N]
    (I : ModelWithCorners ℂ E H) (n : WithTop ℕ∞) {g : Total → N}
    (h : ∀ i e, ContMDiffOn 𝓘(ℂ,ChartCoord) I n (g ∘ chartParam i e) (chartDomain i e)) :
    ContMDiff 𝓘(ℂ,ChartCoord) I n g := by
  intro p
  obtain ⟨⟨i,e⟩,hp⟩ := exists_homeomorphChart_source p
  have hc : ContMDiffAt 𝓘(ℂ,ChartCoord) 𝓘(ℂ,ChartCoord) n (chartCoordinates i e) p :=
    (chartCoordinates_contMDiffOn i e n).contMDiffAt ((chartSource_isOpen i e).mem_nhds hp)
  have hq : chartCoordinates i e p ∈ chartDomain i e := (homeomorphChart i e).map_source hp
  have hf := (h i e).contMDiffAt ((chartDomain_isOpen i e).mem_nhds hq)
  apply (hf.comp p hc).congr_of_eventuallyEq
  filter_upwards [(chartSource_isOpen i e).mem_nhds hp] with p' hp'
  exact congrArg g (chartParam_coordinates i e p' hp').symm

/-- The global blowdown to the actual projective plane is complex analytic. -/
theorem blowdown_contMDiff (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ,ChartCoord) 𝓘(ℂ,ℂ × ℂ) n blowdown := by
  apply contMDiff_of_chartParam
  intro i e
  exact chartParam_blowdown_contMDiffOn i e n

/-- Each of the four actual projective-direction maps is complex analytic. -/
theorem direction_contMDiff (j : Fin 4) (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ,ChartCoord) 𝓘(ℂ) n (fun p => directions p j) := by
  apply contMDiff_of_chartParam
  intro i e
  exact chartParam_direction_contMDiffOn i e j n

/-- The proper family projection is a genuinely complex analytic map. -/
theorem projection_contMDiff (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ,ChartCoord) 𝓘(ℂ) n projection := by
  apply contMDiff_of_chartParam
  intro i e
  exact chartParam_projection_contMDiffOn i e n

/-- The blowdown retaining the family parameter is analytic into the original product family. -/
theorem familyBlowdown_contMDiff (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ,ChartCoord) (𝓘(ℂ,ℂ × ℂ).prod 𝓘(ℂ)) n
      (fun p : Total => (blowdown p,projection p)) :=
  (blowdown_contMDiff n).prodMk (projection_contMDiff n)

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence
