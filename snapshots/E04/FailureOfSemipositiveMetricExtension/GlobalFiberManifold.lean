import FailureOfSemipositiveMetricExtension.GlobalFiberCharts

/-! The actual fixed incidence fibres are compact complex analytic surfaces.
Their charts are the fixed-parameter slices of the verified global threefold
charts, and their inclusions and projective structural maps are analytic. -/

namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiber
noncomputable section
open Set Topology IsManifold
open scoped Manifold ContDiff

theorem insertParameter_contDiff (t : ℂ) (n : WithTop ℕ∞) :
    ContDiff ℂ n (insertParameter t) := contDiff_id.prodMk contDiff_const

/-- Restricted chart changes are precisely the first two coordinates of the global change. -/
theorem transition_contDiffOn (t : ℂ) (i j : Fin 4) (e f : Fin 2) (n : WithTop ℕ∞) :
    ContDiffOn ℂ n ((chart t i e).symm.trans (chart t j f))
      ((chart t i e).symm.trans (chart t j f)).source := by
  have hmap : MapsTo (insertParameter t)
      ((chart t i e).symm.trans (chart t j f)).source
      ((homeomorphChart i e).symm.trans (homeomorphChart j f)).source := by
    intro q hq
    exact ⟨hq.1,hq.2⟩
  have h := (GlobalIncidence.transition_contDiffOn i j e f n).comp
    (insertParameter_contDiff t n).contDiffOn hmap
  exact contDiff_fst.comp_contDiffOn h

theorem atlas_contDiffOn (t : ℂ) (n : WithTop ℕ∞)
    (c c' : PartialHomeomorph (Fiber t) Coord)
    (hc : c ∈ atlas Coord (Fiber t)) (hc' : c' ∈ atlas Coord (Fiber t)) :
    ContDiffOn ℂ n (c.symm.trans c') (c.symm.trans c').source := by
  obtain ⟨i,e,rfl⟩ := (mem_atlas_iff t c).mp hc
  obtain ⟨j,f,rfl⟩ := (mem_atlas_iff t c').mp hc'
  exact transition_contDiffOn t i j e f n

/-- Actual complex surface regularity, including analytic regularity, for every fixed fibre. -/
instance instIsManifoldFiber (t : ℂ) (n : WithTop ℕ∞) : IsManifold 𝓘(ℂ,Coord) n (Fiber t) := by
  apply isManifold_of_contDiffOn
  intro c c' hc hc'
  simpa using atlas_contDiffOn t n c c' hc hc'

theorem complex_analytic_manifold (t : ℂ) : IsManifold 𝓘(ℂ,Coord) ω (Fiber t) := inferInstance

theorem coordinates_contMDiffOn (t : ℂ) (i : Fin 4) (e : Fin 2) (n : WithTop ℕ∞) :
    ContMDiffOn 𝓘(ℂ,Coord) 𝓘(ℂ,Coord) n (coordinates t i e) (source t i e) :=
  contMDiffOn_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (chart_mem_atlas t i e))

theorem param_contMDiffOn (t : ℂ) (i : Fin 4) (e : Fin 2) (n : WithTop ℕ∞) :
    ContMDiffOn 𝓘(ℂ,Coord) 𝓘(ℂ,Coord) n (param t i e) (domain t i e) :=
  contMDiffOn_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (chart_mem_atlas t i e))

/-- Test analyticity on the eight genuine fixed-fibre parametrizations. -/
theorem contMDiff_of_param {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N]
    (t : ℂ) (I : ModelWithCorners ℂ E H) (n : WithTop ℕ∞) {g : Fiber t → N}
    (h : ∀ i e, ContMDiffOn 𝓘(ℂ,Coord) I n (g ∘ param t i e) (domain t i e)) :
    ContMDiff 𝓘(ℂ,Coord) I n g := by
  intro p
  obtain ⟨⟨i,e⟩,hp⟩ := charts_cover t p
  have hc : ContMDiffAt 𝓘(ℂ,Coord) 𝓘(ℂ,Coord) n (coordinates t i e) p :=
    (coordinates_contMDiffOn t i e n).contMDiffAt ((source_isOpen t i e).mem_nhds hp)
  have hq : coordinates t i e p ∈ domain t i e := (chart t i e).map_source hp
  have hf := (h i e).contMDiffAt ((domain_isOpen t i e).mem_nhds hq)
  apply (hf.comp p hc).congr_of_eventuallyEq
  filter_upwards [(source_isOpen t i e).mem_nhds hp] with p' hp'
  exact congrArg g (param_coordinates t i e p' hp').symm

/-- The actual fixed-fibre inclusion into the total analytic threefold is analytic. -/
theorem inclusion_contMDiff (t : ℂ) (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ,Coord) 𝓘(ℂ,ChartCoord) n (inclusion t) := by
  apply contMDiff_of_param
  intro i e
  exact (chartParam_contMDiffOn i e n).comp
    (insertParameter_contDiff t n).contMDiff.contMDiffOn (fun _ h => h)

/-- The projective blowdown on the actual compact fibre. -/
def blowdown (t : ℂ) (p : Fiber t) : PlanePoint := p.val.1

/-- Each of the actual four direction maps on the compact fibre. -/
def direction (t : ℂ) (i : Fin 4) (p : Fiber t) : Direction := p.val.2 i

theorem blowdown_contMDiff (t : ℂ) (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ,Coord) 𝓘(ℂ,ℂ × ℂ) n (blowdown t) :=
  (GlobalIncidence.blowdown_contMDiff n).comp (inclusion_contMDiff t n)

theorem direction_contMDiff (t : ℂ) (i : Fin 4) (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ,Coord) 𝓘(ℂ) n (direction t i) :=
  (GlobalIncidence.direction_contMDiff i n).comp (inclusion_contMDiff t n)

/-- The fixed-fibre blowdown is proper because its domain is the actual compact surface. -/
theorem blowdown_isProperMap (t : ℂ) : IsProperMap (blowdown t) :=
  (blowdown_contMDiff t 0).continuous.isProperMap

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiber
