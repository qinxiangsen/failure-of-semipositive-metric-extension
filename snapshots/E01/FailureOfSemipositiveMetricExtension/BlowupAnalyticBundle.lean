import FailureOfSemipositiveMetricExtension.BlowupBundleSections
import FailureOfSemipositiveMetricExtension.BlowupManifold
import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-! Complex-analytic regularity of the actual glued exceptional-coordinate bundle.
This upgrades its topology to mathlib's `ContMDiffVectorBundle` structure. -/
namespace FailureOfSemipositiveMetricExtension.BlowupLineBundle
noncomputable section
open FailureOfSemipositiveMetricExtension.Blowup FailureOfSemipositiveMetricExtension.BlowupSections Set Bundle
open scoped Manifold ContDiff Topology

theorem coordinatesX_contMDiffOn (n : WithTop ℕ∞) :
    ContMDiffOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) n coordinatesX chartXSet := by
  change ContMDiffOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) n homeomorphChartX homeomorphChartX.source
  apply contMDiffOn_of_mem_maximalAtlas
  apply StructureGroupoid.subset_maximalAtlas
  exact (mem_atlas_iff homeomorphChartX).mpr (Or.inl rfl)

theorem coordinatesY_contMDiffOn (n : WithTop ℕ∞) :
    ContMDiffOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) n coordinatesY chartYSet := by
  change ContMDiffOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) n homeomorphChartY homeomorphChartY.source
  apply contMDiffOn_of_mem_maximalAtlas
  apply StructureGroupoid.subset_maximalAtlas
  exact (mem_atlas_iff homeomorphChartY).mpr (Or.inr rfl)

theorem gain_contMDiffOn (k : ℕ) (n : WithTop ℕ∞) (i j : Bool) :
    ContMDiffOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) n (gain k i j) (baseSet i ∩ baseSet j) := by
  cases i <;> cases j
  · exact contMDiffOn_const
  · have hf : ContDiff ℂ n (fun q : ℂ × ℂ => q.2 ^ k) := by fun_prop
    exact (hf.contMDiff.comp_contMDiffOn (coordinatesY_contMDiffOn n)).mono
      inter_subset_right
  · have hf : ContDiff ℂ n (fun q : ℂ × ℂ => q.2 ^ k) := by fun_prop
    exact (hf.contMDiff.comp_contMDiffOn (coordinatesX_contMDiffOn n)).mono
      inter_subset_right
  · exact contMDiffOn_const

/-- The gluing functions are genuinely complex analytic as manifold functions. -/
instance core_isContMDiff (k : ℕ) (n : WithTop ℕ∞) :
    (core k).IsContMDiff 𝓘(ℂ, ℂ × ℂ) n where
  contMDiffOn_coordChange i j := (gain_contMDiffOn k n i j).smul contMDiffOn_const

theorem actual_analytic_vectorBundle (k : ℕ) :
    ContMDiffVectorBundle ω ℂ (core k).Fiber 𝓘(ℂ, ℂ × ℂ) := inferInstance

theorem coefficient_contMDiffOn {k : ℕ} (a : SectionData k) (n : WithTop ℕ∞)
    (hx : ContDiff ℂ n a.x) (hy : ContDiff ℂ n a.y) (i : Bool) :
    ContMDiffOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) n (coefficient a i) (baseSet i) := by
  cases i
  · exact hx.contMDiff.comp_contMDiffOn (coordinatesX_contMDiffOn n)
  · exact hy.contMDiff.comp_contMDiffOn (coordinatesY_contMDiffOn n)

/-- Coherent analytic coefficients give an analytic section of the actual bundle. -/
theorem sectionMap_contMDiff {k : ℕ} (a : SectionData k) (n : WithTop ℕ∞)
    (hx : ContDiff ℂ n a.x) (hy : ContDiff ℂ n a.y) :
    ContMDiff 𝓘(ℂ, ℂ × ℂ) (𝓘(ℂ, ℂ × ℂ).prod 𝓘(ℂ, ℂ)) n (sectionMap a) := by
  intro p
  let i := (core k).indexAt p
  have hp : p ∈ baseSet i := (core k).mem_baseSet_at p
  let e := (core k).localTriv i
  haveI : MemTrivializationAtlas e := ⟨⟨i,rfl⟩⟩
  apply (e.contMDiffAt_iff (show sectionMap a p ∈ e.source from hp)).mpr
  refine ⟨contMDiffAt_id,?_⟩
  have hnb : baseSet i ∈ 𝓝 p := (core k).isOpen_baseSet i |>.mem_nhds hp
  exact ((coefficient_contMDiffOn a n hx hy i).congr
    (fun q hq => congrArg Prod.snd (sectionMap_localTriv a i q hq))).contMDiffAt hnb

/-- The concrete central polynomial coefficients are analytic in both chart variables. -/
theorem cubic_coefficients_contDiff (n : WithTop ℕ∞) (i : Fin 4) :
    ContDiff ℂ n (cubicSystem₁ i).x ∧ ContDiff ℂ n (cubicSystem₁ i).y ∧
    ContDiff ℂ n (cubicSystem₂ i).x ∧ ContDiff ℂ n (cubicSystem₂ i).y ∧
    ContDiff ℂ n (cubicSystem₃ i).x ∧ ContDiff ℂ n (cubicSystem₃ i).y ∧
    ContDiff ℂ n (cubicSystem₄ i).x ∧ ContDiff ℂ n (cubicSystem₄ i).y := by
  fin_cases i <;> dsimp [cubicSystem₁,cubicSystem₂,cubicSystem₃,cubicSystem₄,
    FailureOfSemipositiveMetricExtension.BlowupSections.x₁,FailureOfSemipositiveMetricExtension.BlowupSections.y₁,
    FailureOfSemipositiveMetricExtension.BlowupSections.x₂,FailureOfSemipositiveMetricExtension.BlowupSections.y₂,
    FailureOfSemipositiveMetricExtension.BlowupSections.x₃,FailureOfSemipositiveMetricExtension.BlowupSections.y₃,
    FailureOfSemipositiveMetricExtension.BlowupSections.x₄,FailureOfSemipositiveMetricExtension.BlowupSections.y₄]
  all_goals repeat' constructor
  all_goals fun_prop

theorem central_actual_sections_analytic (i : Fin 4) :
    ContMDiff 𝓘(ℂ, ℂ × ℂ) (𝓘(ℂ, ℂ × ℂ).prod 𝓘(ℂ, ℂ)) ω (sectionMap (cubicSystem₁ i)) ∧
    ContMDiff 𝓘(ℂ, ℂ × ℂ) (𝓘(ℂ, ℂ × ℂ).prod 𝓘(ℂ, ℂ)) ω (sectionMap (cubicSystem₂ i)) ∧
    ContMDiff 𝓘(ℂ, ℂ × ℂ) (𝓘(ℂ, ℂ × ℂ).prod 𝓘(ℂ, ℂ)) ω (sectionMap (cubicSystem₃ i)) ∧
    ContMDiff 𝓘(ℂ, ℂ × ℂ) (𝓘(ℂ, ℂ × ℂ).prod 𝓘(ℂ, ℂ)) ω (sectionMap (cubicSystem₄ i)) := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := cubic_coefficients_contDiff ω i
  exact ⟨sectionMap_contMDiff _ ω h1 h2,sectionMap_contMDiff _ ω h3 h4,
    sectionMap_contMDiff _ ω h5 h6,sectionMap_contMDiff _ ω h7 h8⟩

open FailureOfSemipositiveMetricExtension.PencilSections in
theorem pencil_coefficients_contDiff (t : ℂ) (n : WithTop ℕ∞) (i : Fin 2) :
    ContDiff ℂ n (pencilSystem₁ t i).x ∧ ContDiff ℂ n (pencilSystem₁ t i).y ∧
    ContDiff ℂ n (pencilSystem₂ t i).x ∧ ContDiff ℂ n (pencilSystem₂ t i).y ∧
    ContDiff ℂ n (pencilSystem₃ t i).x ∧ ContDiff ℂ n (pencilSystem₃ t i).y ∧
    ContDiff ℂ n (pencilSystem₄ t i).x ∧ ContDiff ℂ n (pencilSystem₄ t i).y := by
  fin_cases i <;> dsimp [pencilSystem₁,pencilSystem₂,pencilSystem₃,pencilSystem₄,
    FailureOfSemipositiveMetricExtension.PencilSections.x₁,FailureOfSemipositiveMetricExtension.PencilSections.y₁,
    FailureOfSemipositiveMetricExtension.PencilSections.x₂,FailureOfSemipositiveMetricExtension.PencilSections.y₂,
    FailureOfSemipositiveMetricExtension.PencilSections.x₃,FailureOfSemipositiveMetricExtension.PencilSections.y₃,
    FailureOfSemipositiveMetricExtension.PencilSections.x₄,FailureOfSemipositiveMetricExtension.PencilSections.y₄]
  all_goals repeat' constructor
  all_goals fun_prop

open FailureOfSemipositiveMetricExtension.PencilSections in
theorem nearby_actual_sections_analytic (t : ℂ) (i : Fin 2) :
    ContMDiff 𝓘(ℂ, ℂ × ℂ) (𝓘(ℂ, ℂ × ℂ).prod 𝓘(ℂ, ℂ)) ω (sectionMap (pencilSystem₁ t i)) ∧
    ContMDiff 𝓘(ℂ, ℂ × ℂ) (𝓘(ℂ, ℂ × ℂ).prod 𝓘(ℂ, ℂ)) ω (sectionMap (pencilSystem₂ t i)) ∧
    ContMDiff 𝓘(ℂ, ℂ × ℂ) (𝓘(ℂ, ℂ × ℂ).prod 𝓘(ℂ, ℂ)) ω (sectionMap (pencilSystem₃ t i)) ∧
    ContMDiff 𝓘(ℂ, ℂ × ℂ) (𝓘(ℂ, ℂ × ℂ).prod 𝓘(ℂ, ℂ)) ω (sectionMap (pencilSystem₄ t i)) := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := pencil_coefficients_contDiff t ω i
  exact ⟨sectionMap_contMDiff _ ω h1 h2,sectionMap_contMDiff _ ω h3 h4,
    sectionMap_contMDiff _ ω h5 h6,sectionMap_contMDiff _ ω h7 h8⟩

end
end FailureOfSemipositiveMetricExtension.BlowupLineBundle
