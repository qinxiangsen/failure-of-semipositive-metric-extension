import FailureOfSemipositiveMetricExtension.BlowupCharts
import Mathlib.Geometry.Manifold.ChartedSpace

/-!
A genuine topology and charted-space structure on the incidence blow-up, constructed
from the two affine charts and their verified transition maps. This is an atlas-generated
topology; no pre-existing topology on mathlib's projective quotient is assumed.
-/

noncomputable section

namespace FailureOfSemipositiveMetricExtension.Blowup

open Set

attribute [local instance] Classical.propDecidable

/-- Globally extended first coordinates; only their values on `chartXSet` matter. -/
def coordinatesX : Point → ℂ × ℂ := Function.invFun (fun q : ℂ × ℂ => X q.1 q.2)
/-- Globally extended second coordinates; only their values on `chartYSet` matter. -/
def coordinatesY : Point → ℂ × ℂ := Function.invFun (fun q : ℂ × ℂ => Y q.1 q.2)

@[simp] theorem coordinatesX_X (q : ℂ × ℂ) : coordinatesX (X q.1 q.2) = q :=
  Function.leftInverse_invFun X_injective q
@[simp] theorem coordinatesY_Y (q : ℂ × ℂ) : coordinatesY (Y q.1 q.2) = q :=
  Function.leftInverse_invFun Y_injective q

theorem X_coordinatesX (p : Point) (hp : p ∈ chartXSet) :
    X (coordinatesX p).1 (coordinatesX p).2 = p := by
  rw [chartXSet_eq_range] at hp
  rcases hp with ⟨q,rfl⟩
  rw [coordinatesX_X]

theorem Y_coordinatesY (p : Point) (hp : p ∈ chartYSet) :
    Y (coordinatesY p).1 (coordinatesY p).2 = p := by
  rw [chartYSet_eq_range] at hp
  rcases hp with ⟨q,rfl⟩
  rw [coordinatesY_Y]

def partialChartX : PartialEquiv Point (ℂ × ℂ) where
  toFun := coordinatesX
  invFun q := X q.1 q.2
  source := chartXSet
  target := univ
  map_source' _ _ := mem_univ _
  map_target' q _ := ⟨q.2,rfl⟩
  left_inv' := X_coordinatesX
  right_inv' q _ := coordinatesX_X q

def partialChartY : PartialEquiv Point (ℂ × ℂ) where
  toFun := coordinatesY
  invFun q := Y q.1 q.2
  source := chartYSet
  target := univ
  map_source' _ _ := mem_univ _
  map_target' q _ := ⟨q.2,rfl⟩
  left_inv' := Y_coordinatesY
  right_inv' q _ := coordinatesY_Y q

@[simp] theorem partialChartX_source : partialChartX.source = chartXSet := rfl
@[simp] theorem partialChartY_source : partialChartY.source = chartYSet := rfl
@[simp] theorem partialChartX_target : partialChartX.target = univ := rfl
@[simp] theorem partialChartY_target : partialChartY.target = univ := rfl
@[simp] theorem partialChartX_symm_apply (q : ℂ × ℂ) :
    partialChartX.symm q = X q.1 q.2 := rfl
@[simp] theorem partialChartY_symm_apply (q : ℂ × ℂ) :
    partialChartY.symm q = Y q.1 q.2 := rfl

theorem coordinatesY_X (q : ℂ × ℂ) (hq : q.2 ≠ 0) :
    coordinatesY (X q.1 q.2) = transition q := by
  rw [X_eq_Y_transition q.1 q.2 hq]
  exact coordinatesY_Y (transition q)

theorem coordinatesX_Y (q : ℂ × ℂ) (hq : q.2 ≠ 0) :
    coordinatesX (Y q.1 q.2) = transition q := by
  rw [Y_eq_X_transition q.1 q.2 hq]
  exact coordinatesX_X (transition q)

@[simp] theorem transitionXX_source :
    (partialChartX.symm.trans partialChartX).source = univ := by
  ext q
  simp [PartialEquiv.trans_source,partialChartX,chartXSet]

@[simp] theorem transitionYY_source :
    (partialChartY.symm.trans partialChartY).source = univ := by
  ext q
  simp [PartialEquiv.trans_source,partialChartY,chartYSet]

@[simp] theorem transitionXY_source :
    (partialChartX.symm.trans partialChartY).source = overlap := by
  ext q
  simp [PartialEquiv.trans_source,overlap]

@[simp] theorem transitionYX_source :
    (partialChartY.symm.trans partialChartX).source = overlap := by
  ext q
  simp [PartialEquiv.trans_source,overlap]

@[simp] theorem transitionXX_apply (q : ℂ × ℂ) :
    (partialChartX.symm.trans partialChartX) q = q := coordinatesX_X q
@[simp] theorem transitionYY_apply (q : ℂ × ℂ) :
    (partialChartY.symm.trans partialChartY) q = q := coordinatesY_Y q

theorem transitionXY_apply (q : ℂ × ℂ) (hq : q ∈ overlap) :
    (partialChartX.symm.trans partialChartY) q = transition q := coordinatesY_X q hq

theorem transitionYX_apply (q : ℂ × ℂ) (hq : q ∈ overlap) :
    (partialChartY.symm.trans partialChartX) q = transition q := coordinatesX_Y q hq

/-- Two genuine partial equivalences, with all chart-domain and continuity obligations proved. -/
def atlasCore : ChartedSpaceCore (ℂ × ℂ) Point where
  atlas := {partialChartX,partialChartY}
  chartAt p := if p ∈ chartXSet then partialChartX else partialChartY
  mem_chart_source p := by
    split_ifs with hp
    · exact hp
    · have hc : p ∈ chartXSet ∪ chartYSet := by rw [chart_sets_cover]; trivial
      exact hc.resolve_left hp
  chart_mem_atlas p := by
    split_ifs <;> simp
  open_source e e' he he' := by
    simp only [mem_insert_iff,mem_singleton_iff] at he he'
    rcases he with rfl | rfl <;> rcases he' with rfl | rfl
    · rw [transitionXX_source]; exact isOpen_univ
    · rw [transitionXY_source]; exact overlap_isOpen
    · rw [transitionYX_source]; exact overlap_isOpen
    · rw [transitionYY_source]; exact isOpen_univ
  continuousOn_toFun e e' he he' := by
    simp only [mem_insert_iff,mem_singleton_iff] at he he'
    rcases he with rfl | rfl <;> rcases he' with rfl | rfl
    · exact continuousOn_id.congr (fun q _ => transitionXX_apply q)
    · rw [transitionXY_source]
      exact transition_continuousOn.congr transitionXY_apply
    · rw [transitionYX_source]
      exact transition_continuousOn.congr transitionYX_apply
    · exact continuousOn_id.congr (fun q _ => transitionYY_apply q)

/-- The topology on the incidence blow-up generated by the two affine charts. -/
instance instTopologicalSpacePoint : TopologicalSpace Point := atlasCore.toTopologicalSpace

/-- The incidence blow-up is a genuine charted space modelled on the complex affine plane. -/
instance instChartedSpacePoint : ChartedSpace (ℂ × ℂ) Point := atlasCore.toChartedSpace

/-- The first affine chart, now a genuine partial homeomorphism. -/
def homeomorphChartX : PartialHomeomorph Point (ℂ × ℂ) :=
  atlasCore.partialHomeomorph partialChartX (by simp [atlasCore])

/-- The second affine chart, now a genuine partial homeomorphism. -/
def homeomorphChartY : PartialHomeomorph Point (ℂ × ℂ) :=
  atlasCore.partialHomeomorph partialChartY (by simp [atlasCore])

@[simp] theorem homeomorphChartX_source : homeomorphChartX.source = chartXSet := rfl
@[simp] theorem homeomorphChartY_source : homeomorphChartY.source = chartYSet := rfl
@[simp] theorem homeomorphChartX_target : homeomorphChartX.target = univ := rfl
@[simp] theorem homeomorphChartY_target : homeomorphChartY.target = univ := rfl

/-- Both affine chart domains are open in the constructed topology. -/
theorem chartXSet_isOpen : IsOpen chartXSet := homeomorphChartX.open_source

theorem chartYSet_isOpen : IsOpen chartYSet := homeomorphChartY.open_source

theorem X_continuous : Continuous (fun q : ℂ × ℂ => X q.1 q.2) := by
  exact continuous_iff_continuousOn_univ.mpr homeomorphChartX.continuousOn_symm

theorem Y_continuous : Continuous (fun q : ℂ × ℂ => Y q.1 q.2) := by
  exact continuous_iff_continuousOn_univ.mpr homeomorphChartY.continuousOn_symm

/-- The blow-down projection is continuous for the constructed atlas topology. -/
theorem projection_continuous : Continuous projection := by
  refine continuous_iff_continuousAt.mpr fun p => ?_
  rcases charts_cover p with ⟨r,s,rfl⟩ | ⟨r,s,rfl⟩
  · apply (homeomorphChartX.symm.continuousAt_iff_continuousAt_comp_right
      (show X r s ∈ homeomorphChartX.source from ⟨s,rfl⟩)).mpr
    have hc : Continuous (projection ∘ homeomorphChartX.symm) := by
      apply continuous_pi
      intro i
      fin_cases i
      · exact continuous_fst
      · exact continuous_fst.mul continuous_snd
    exact hc.continuousAt
  · apply (homeomorphChartY.symm.continuousAt_iff_continuousAt_comp_right
      (show Y r s ∈ homeomorphChartY.source from ⟨s,rfl⟩)).mpr
    have hc : Continuous (projection ∘ homeomorphChartY.symm) := by
      apply continuous_pi
      intro i
      fin_cases i
      · exact continuous_fst.mul continuous_snd
      · exact continuous_fst
    exact hc.continuousAt

/-- In particular the exceptional divisor is a closed subset of the blow-up. -/
theorem exceptional_isClosed : IsClosed {p : Point | projection p = 0} :=
  isClosed_singleton.preimage projection_continuous

/-- The affine parametrizations are open embeddings, not merely set injections. -/
theorem X_isOpenEmbedding : Topology.IsOpenEmbedding (fun q : ℂ × ℂ => X q.1 q.2) :=
  homeomorphChartX.symm.to_isOpenEmbedding rfl

theorem Y_isOpenEmbedding : Topology.IsOpenEmbedding (fun q : ℂ × ℂ => Y q.1 q.2) :=
  homeomorphChartY.symm.to_isOpenEmbedding rfl

/-- A finite cover by second-countable affine charts makes the blow-up second countable. -/
instance instSecondCountableTopologyPoint : SecondCountableTopology Point := by
  let U : Bool → Set Point := fun b => if b then chartXSet else chartYSet
  haveI : ∀ b, SecondCountableTopology (U b) := by
    intro b
    cases b
    · exact homeomorphChartY.secondCountableTopology_source
    · exact homeomorphChartX.secondCountableTopology_source
  apply TopologicalSpace.secondCountableTopology_of_countable_cover (U := U)
  · intro b
    cases b
    · exact chartYSet_isOpen
    · exact chartXSet_isOpen
  · ext p
    simp only [mem_iUnion,mem_univ,iff_true]
    rcases direction_cover (direction p) with hx | hy
    · exact ⟨true,hx⟩
    · exact ⟨false,hy⟩

end FailureOfSemipositiveMetricExtension.Blowup
