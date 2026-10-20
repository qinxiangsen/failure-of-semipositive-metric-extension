import FailureOfSemipositiveMetricExtension.GlobalAnalyticMaps

/-! Eight genuine affine charts on each existing fixed incidence fibre. The
original subspace topology on `Fiber t` is retained throughout. -/

namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiber
noncomputable section
open Set Topology

abbrev Coord := ℂ × ℂ

/-- The actual inclusion of the independently defined fibre into the total space. -/
def inclusion (t : ℂ) (p : Fiber t) : Total :=
  ⟨(p.val.1,p.val.2,t),p.property⟩

@[simp] theorem projection_inclusion (t : ℂ) (p : Fiber t) : projection (inclusion t p) = t := rfl
@[simp] theorem blowdown_inclusion (t : ℂ) (p : Fiber t) : blowdown (inclusion t p) = p.val.1 := rfl
@[simp] theorem directions_inclusion (t : ℂ) (p : Fiber t) : directions (inclusion t p) = p.val.2 := rfl

theorem inclusion_injective (t : ℂ) : Function.Injective (inclusion t) := by
  intro p q h
  apply Subtype.ext
  exact Prod.ext (congrArg blowdown h) (congrArg directions h)

theorem inclusion_continuous (t : ℂ) : Continuous (inclusion t) :=
  ((continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_snd.comp continuous_subtype_val).prodMk continuous_const)).subtype_mk _

theorem inclusion_isClosedEmbedding (t : ℂ) : Topology.IsClosedEmbedding (inclusion t) :=
  (inclusion_continuous t).isClosedEmbedding (inclusion_injective t)

instance instT2SpaceFiber (t : ℂ) : T2Space (Fiber t) :=
  (inclusion_isClosedEmbedding t).isEmbedding.t2Space

instance instSecondCountableTopologyFiber (t : ℂ) : SecondCountableTopology (Fiber t) :=
  (inclusion_isClosedEmbedding t).isEmbedding.isInducing.secondCountableTopology

/-- Insert the fixed family parameter in the global affine coordinates. -/
def insertParameter (t : ℂ) (q : Coord) : ChartCoord := (q,t)

theorem insertParameter_continuous (t : ℂ) : Continuous (insertParameter t) :=
  continuous_id.prodMk continuous_const

/-- The actual restricted global parametrization in the fixed fibre. -/
def param (t : ℂ) (i : Fin 4) (e : Fin 2) (q : Coord) : Fiber t :=
  ⟨((chartParam i e (q,t)).val.1,(chartParam i e (q,t)).val.2.1),
    (chartParam i e (q,t)).property⟩

@[simp] theorem inclusion_param (t : ℂ) (i : Fin 4) (e : Fin 2) (q : Coord) :
    inclusion t (param t i e q) = chartParam i e (q,t) := rfl

def source (t : ℂ) (i : Fin 4) (e : Fin 2) : Set (Fiber t) :=
  inclusion t ⁻¹' chartSource i e

def domain (t : ℂ) (i : Fin 4) (e : Fin 2) : Set Coord :=
  insertParameter t ⁻¹' chartDomain i e

def coordinates (t : ℂ) (i : Fin 4) (e : Fin 2) (p : Fiber t) : Coord :=
  (chartCoordinates i e (inclusion t p)).1

theorem global_coordinates_eq (t : ℂ) (i : Fin 4) (e : Fin 2) (p : Fiber t)
    (hp : p ∈ source t i e) :
    chartCoordinates i e (inclusion t p) = (coordinates t i e p,t) := by
  apply Prod.ext
  · rfl
  · rw [chartCoordinates_eq_explicit i e _ hp]
    rfl

@[simp] theorem coordinates_param (t : ℂ) (i : Fin 4) (e : Fin 2) (q : Coord) :
    coordinates t i e (param t i e q) = q := by
  simp [coordinates]

theorem param_coordinates (t : ℂ) (i : Fin 4) (e : Fin 2) (p : Fiber t)
    (hp : p ∈ source t i e) : param t i e (coordinates t i e p) = p := by
  apply inclusion_injective t
  rw [inclusion_param,← global_coordinates_eq t i e p hp]
  exact chartParam_coordinates i e _ hp

theorem source_isOpen (t : ℂ) (i : Fin 4) (e : Fin 2) : IsOpen (source t i e) :=
  (chartSource_isOpen i e).preimage (inclusion_continuous t)

theorem domain_isOpen (t : ℂ) (i : Fin 4) (e : Fin 2) : IsOpen (domain t i e) :=
  (chartDomain_isOpen i e).preimage (insertParameter_continuous t)

theorem coordinates_continuousOn (t : ℂ) (i : Fin 4) (e : Fin 2) :
    ContinuousOn (coordinates t i e) (source t i e) :=
  continuous_fst.comp_continuousOn ((chartCoordinates_continuousOn i e).comp
    (inclusion_continuous t).continuousOn (fun _ h => h))

theorem param_continuousOn (t : ℂ) (i : Fin 4) (e : Fin 2) :
    ContinuousOn (param t i e) (domain t i e) := by
  apply (inclusion_isClosedEmbedding t).isEmbedding.isInducing.continuousOn_iff.mpr
  exact (chartParam_continuousOn i e).comp (insertParameter_continuous t).continuousOn
    (fun _ h => h)

/-- A genuine partial homeomorphism onto a fixed-parameter slice of each global domain. -/
def chart (t : ℂ) (i : Fin 4) (e : Fin 2) : PartialHomeomorph (Fiber t) Coord where
  toFun := coordinates t i e
  invFun := param t i e
  source := source t i e
  target := domain t i e
  map_source' p hp := by
    have h := (homeomorphChart i e).map_source hp
    change chartCoordinates i e (inclusion t p) ∈ chartDomain i e at h
    rw [global_coordinates_eq t i e p hp] at h
    exact h
  map_target' q hq := by
    change inclusion t (param t i e q) ∈ chartSource i e
    rw [inclusion_param]
    exact (homeomorphChart i e).map_target hq
  left_inv' := param_coordinates t i e
  right_inv' q _ := coordinates_param t i e q
  open_source := source_isOpen t i e
  open_target := domain_isOpen t i e
  continuousOn_toFun := coordinates_continuousOn t i e
  continuousOn_invFun := param_continuousOn t i e

/-- The eight restricted charts cover every point of each actual fixed fibre. -/
theorem charts_cover (t : ℂ) (p : Fiber t) : ∃ k : Fin 4 × Fin 2, p ∈ (chart t k.1 k.2).source := by
  obtain ⟨k,hk⟩ := exists_homeomorphChart_source (inclusion t p)
  exact ⟨k,hk⟩

def chartIndex (t : ℂ) (p : Fiber t) : Fin 4 × Fin 2 := Classical.choose (charts_cover t p)

theorem chartIndex_mem_source (t : ℂ) (p : Fiber t) :
    p ∈ (chart t (chartIndex t p).1 (chartIndex t p).2).source :=
  Classical.choose_spec (charts_cover t p)

/-- The actual fixed fibre is charted by complex affine two-space. -/
instance instChartedSpaceFiber (t : ℂ) : ChartedSpace Coord (Fiber t) where
  atlas := range (fun k : Fin 4 × Fin 2 => chart t k.1 k.2)
  chartAt p := chart t (chartIndex t p).1 (chartIndex t p).2
  mem_chart_source := chartIndex_mem_source t
  chart_mem_atlas p := ⟨chartIndex t p,rfl⟩

theorem mem_atlas_iff (t : ℂ) (c : PartialHomeomorph (Fiber t) Coord) :
    c ∈ atlas Coord (Fiber t) ↔ ∃ i e, c = chart t i e := by
  change (∃ k : Fin 4 × Fin 2, chart t k.1 k.2 = c) ↔ _
  constructor
  · rintro ⟨k,hk⟩
    exact ⟨k.1,k.2,hk.symm⟩
  · rintro ⟨i,e,rfl⟩
    exact ⟨(i,e),rfl⟩

theorem chart_mem_atlas (t : ℂ) (i : Fin 4) (e : Fin 2) :
    chart t i e ∈ atlas Coord (Fiber t) := (mem_atlas_iff t _).mpr ⟨i,e,rfl⟩

/-- No replacement of the already defined fibre subspace topology has occurred. -/
theorem fiber_topology_instance_unchanged (t : ℂ) :
    (inferInstance : TopologicalSpace (Fiber t)) = instTopologicalSpaceFiber t := rfl

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiber
