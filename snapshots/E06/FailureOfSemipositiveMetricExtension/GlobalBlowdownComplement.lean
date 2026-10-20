import FailureOfSemipositiveMetricExtension.GlobalAmbientImmersion
import FailureOfSemipositiveMetricExtension.GlobalExceptionalDensity

/-! The actual family blow-down is a two-sided analytic isomorphism off its four
moving centres.  Both sets carry their existing analytic topology.  The inverse
is certified through locally normalized polynomial vectors; no regularity of a
chosen projective representative is used. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence
noncomputable section
open Set Topology IsManifold
open scoped Manifold ContDiff

/-- Analyticity into the actual incidence threefold follows from its actual
ambient inclusion, using the verified local analytic retractions. -/
theorem contMDiffAt_of_ambient_inclusion {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
    [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℂ E H) (n : WithTop ℕ∞) {g : M → Total} {x : M}
    (hg : ContMDiffAt I ambientModel n (fun y => (g y).val) x) :
    ContMDiffAt I 𝓘(ℂ,ChartCoord) n g x := by
  obtain ⟨⟨r,e⟩,hx⟩ := exists_homeomorphChart_source (g x)
  have hc : ContinuousAt g x := hg.continuousAt.codRestrict _
  apply ((ambientRetraction_contMDiffAt r e n (g x) hx).comp x hg).congr_of_eventuallyEq
  filter_upwards [hc.eventually ((chartSource_isOpen r e).mem_nhds hx)] with y hy
  exact (ambientRetraction_inclusion r e (g y) hy).symm

namespace BlowdownComplement

abbrev Base := PlanePoint × ℂ
abbrev baseModel := 𝓘(ℂ,ℂ × ℂ).prod 𝓘(ℂ)

def baseAway : Set Base := {q | ∀ r, q.1 ≠ centre r q.2}

def down (p : Total) : Base := (blowdown p,projection p)

/-- The canonical lift; its analyticity is asserted only off the centres. -/
def lift (q : Base) : Total :=
  ⟨(q.1,(fun r => chosenDirection q.1 r q.2),q.2),
    fun r => chosenDirection_incidence q.1 r q.2⟩

@[simp] theorem down_lift (q : Base) : down (lift q) = q := rfl

@[simp] theorem lift_direction (q : Base) (r : Fin 4) :
    directions (lift q) r = chosenDirection q.1 r q.2 := rfl

theorem lift_down (p : Total) (hp : p ∈ awayCentres) : lift (down p) = p := by
  apply total_ext (p := lift (down p)) (q := p) rfl _ rfl
  funext r
  exact directions_eq_away (lift (down p)) p r rfl rfl (hp r)

theorem down_mem_baseAway_iff (p : Total) : down p ∈ baseAway ↔ p ∈ awayCentres := Iff.rfl

theorem lift_mem_awayCentres_iff (q : Base) : lift q ∈ awayCentres ↔ q ∈ baseAway := Iff.rfl

theorem baseAway_isOpen : IsOpen baseAway := by
  rw [baseAway,setOf_forall]
  apply isOpen_iInter_of_finite
  intro r
  exact isOpen_ne_fun continuous_fst ((centre_continuous r).comp continuous_snd)

theorem baseAway_dense : Dense baseAway :=
  blowdown_projection_surjective.denseRange.dense_of_mapsTo
    (familyBlowdown_contMDiff 0).continuous awayCentres_dense (fun _ h => h)

/-- The local homogeneous pair is nonzero precisely where the indicated centre
is avoided. This statement uses arbitrary actual homogeneous coordinates. -/
theorem pair_nonzero_of_mk_away (v : Fin 3 → ℂ) (hv : v ≠ 0) (r : Fin 4) (t : ℂ)
    (h : Projectivization.mk ℂ v hv ≠ centre r t) : pairMap r t v ≠ 0 := by
  intro hz
  exact h ((projective_eq_iff_mem v hv (centre r t)).mpr
    ((pairMap_zero_iff_mem_centre r t v).mp hz))

theorem chosenDirection_mk (v : Fin 3 → ℂ) (hv : v ≠ 0) (r : Fin 4) (t : ℂ)
    (h : Projectivization.mk ℂ v hv ≠ centre r t) :
    chosenDirection (Projectivization.mk ℂ v hv) r t = ProjectiveLine.vectorPoint (pairMap r t v) := by
  have hn := pair_nonzero_of_mk_away v hv r t h
  rw [ProjectiveLine.vectorPoint_eq_mk _ hn]
  symm
  exact (projective_eq_iff_mem _ hn _).mpr
    ((incidence_mk_iff v hv _ r t).mp (chosenDirection_incidence _ r t))

def normalizedPair (a : Fin 3) (r : Fin 4) (q : Base) : Blowup.Plane :=
  pairMap r q.2 (ProjectivePlane.vector a (ProjectivePlane.coordinates a q.1))

theorem normalizedPair_nonzero (a : Fin 3) (r : Fin 4) (q : Base)
    (ha : q.1 ∈ ProjectivePlane.chartSet a) (hr : q.1 ≠ centre r q.2) :
    normalizedPair a r q ≠ 0 := by
  apply pair_nonzero_of_mk_away _ (ProjectivePlane.vector_nonzero a _) r q.2
  change ProjectivePlane.param a (ProjectivePlane.coordinates a q.1) ≠ _
  rwa [ProjectivePlane.param_coordinates a q.1 ha]

theorem chosenDirection_normalized (a : Fin 3) (r : Fin 4) (q : Base)
    (ha : q.1 ∈ ProjectivePlane.chartSet a) (hr : q.1 ≠ centre r q.2) :
    chosenDirection q.1 r q.2 = ProjectiveLine.vectorPoint (normalizedPair a r q) := by
  have h := chosenDirection_mk (ProjectivePlane.vector a (ProjectivePlane.coordinates a q.1))
    (ProjectivePlane.vector_nonzero a _) r q.2
  change (ProjectivePlane.param a (ProjectivePlane.coordinates a q.1) ≠ _) →
    chosenDirection (ProjectivePlane.param a (ProjectivePlane.coordinates a q.1)) r q.2 = _ at h
  rw [ProjectivePlane.param_coordinates a q.1 ha] at h
  exact h hr

set_option maxHeartbeats 800000 in
theorem normalizedPair_contMDiffAt (a : Fin 3) (r : Fin 4) (n : WithTop ℕ∞)
    (q : Base) (ha : q.1 ∈ ProjectivePlane.chartSet a) :
    ContMDiffAt baseModel 𝓘(ℂ,Blowup.Plane) n (normalizedPair a r) q := by
  have hb : ContMDiffAt baseModel 𝓘(ℂ,ℂ × ℂ) n
      (fun q : Base => ProjectivePlane.coordinates a q.1) q :=
    ((planeCoordinates_contMDiffOn a n).contMDiffAt
    ((ProjectivePlane.chartSet_isOpen a).mem_nhds ha)).comp q contMDiffAt_fst
  have hv := (normalizedVector_contDiff a n).contMDiff.contMDiffAt.comp q hb
  exact (pairMap_contDiff r n).contMDiff.contMDiffAt.comp q (contMDiffAt_snd.prodMk_space hv)

theorem chosenDirection_contMDiffAt (r : Fin 4) (n : WithTop ℕ∞) (q : Base)
    (hr : q.1 ≠ centre r q.2) :
    ContMDiffAt baseModel 𝓘(ℂ) n (fun q : Base => chosenDirection q.1 r q.2) q := by
  obtain ⟨a,w,hw⟩ := ProjectivePlane.charts_cover q.1
  have ha : q.1 ∈ ProjectivePlane.chartSet a := hw ▸ ProjectivePlane.param_mem_chartSet a w
  have h := (ProjectiveLine.vectorPoint_contMDiffAt n _ (normalizedPair_nonzero a r q ha hr)).comp q
    (normalizedPair_contMDiffAt a r n q ha)
  apply h.congr_of_eventuallyEq
  have hbase := continuous_fst.continuousAt.eventually ((ProjectivePlane.chartSet_isOpen a).mem_nhds ha)
  have haway := (isOpen_ne_fun continuous_fst ((centre_continuous r).comp continuous_snd)).mem_nhds hr
  filter_upwards [hbase,haway] with q' hb hr'
  exact chosenDirection_normalized a r q' hb hr'

theorem lift_contMDiffAt (n : WithTop ℕ∞) (q : Base) (hq : q ∈ baseAway) :
    ContMDiffAt baseModel 𝓘(ℂ,ChartCoord) n lift q := by
  apply contMDiffAt_of_ambient_inclusion baseModel n
  have hd : ContMDiffAt baseModel 𝓘(ℂ,ProjectiveDirectionProduct.Coord) n
      (fun q : Base => fun r => chosenDirection q.1 r q.2) q := by
    apply ProjectiveDirectionProduct.contMDiffAt_of_components baseModel n
    intro r
    exact chosenDirection_contMDiffAt r n q (hq r)
  exact contMDiffAt_fst.prodMk (hd.prodMk contMDiffAt_snd)

theorem lift_contMDiffOn (n : WithTop ℕ∞) :
    ContMDiffOn baseModel 𝓘(ℂ,ChartCoord) n lift baseAway :=
  fun q hq => (lift_contMDiffAt n q hq).contMDiffWithinAt

/-- Genuine analytic partial homeomorphism between the existing open complements. -/
def partialHomeomorph : PartialHomeomorph Total Base where
  toFun := down
  invFun := lift
  source := awayCentres
  target := baseAway
  map_source' _ h := h
  map_target' _ h := h
  left_inv' := lift_down
  right_inv' q _ := down_lift q
  open_source := awayCentres_isOpen
  open_target := baseAway_isOpen
  continuousOn_toFun := (familyBlowdown_contMDiff 0).continuous.continuousOn
  continuousOn_invFun := (lift_contMDiffOn 0).continuousOn

/-- The underlying two-sided homeomorphism of the actual open subspaces. -/
def homeomorph : awayCentres ≃ₜ baseAway := partialHomeomorph.toHomeomorphSourceTarget

theorem partialHomeomorph_analytic :
    ContMDiffOn 𝓘(ℂ,ChartCoord) baseModel ω partialHomeomorph partialHomeomorph.source ∧
    ContMDiffOn baseModel 𝓘(ℂ,ChartCoord) ω partialHomeomorph.symm partialHomeomorph.target :=
  ⟨(familyBlowdown_contMDiff ω).contMDiffOn,lift_contMDiffOn ω⟩

end BlowdownComplement
end
end FailureOfSemipositiveMetricExtension.GlobalIncidence
