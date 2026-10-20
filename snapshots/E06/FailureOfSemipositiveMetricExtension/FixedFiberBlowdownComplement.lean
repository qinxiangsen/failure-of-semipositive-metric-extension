import FailureOfSemipositiveMetricExtension.GlobalBlowdownComplement
import FailureOfSemipositiveMetricExtension.GlobalFiberExceptionalDensity

/-! Actual dense-open biholomorphisms for every fixed compact fibre.
This is an analytic statement on the original manifolds. No algebraic
rationality, analytification, or scheme-level blow-up identification is asserted. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiber
noncomputable section
open Set Topology IsManifold
open scoped Manifold ContDiff

/-- Analyticity into the actual fixed fibre can be tested by its genuine inclusion. -/
theorem contMDiffAt_of_total_inclusion {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
    [TopologicalSpace M] [ChartedSpace H M]
    (t : ℂ) (I : ModelWithCorners ℂ E H) (n : WithTop ℕ∞)
    {g : M → Fiber t} {x : M}
    (hg : ContMDiffAt I 𝓘(ℂ,ChartCoord) n (fun y => inclusion t (g y)) x) :
    ContMDiffAt I 𝓘(ℂ,Coord) n g x := by
  obtain ⟨⟨r,e⟩,hx⟩ := charts_cover t (g x)
  have hc : ContinuousAt g x :=
    (inclusion_isClosedEmbedding t).isEmbedding.isInducing.continuousAt_iff.mpr hg.continuousAt
  have hcoords := ((chartCoordinates_contMDiffOn r e n).contMDiffAt
    ((chartSource_isOpen r e).mem_nhds hx)).comp x hg
  have hfirst : ContMDiffAt I 𝓘(ℂ,Coord) n (fun y => coordinates t r e (g y)) x :=
    (contDiff_fst.contMDiff.contMDiffAt :
      ContMDiffAt 𝓘(ℂ,ChartCoord) 𝓘(ℂ,Coord) n Prod.fst _).comp x hcoords
  have hparam := (param_contMDiffOn t r e n).contMDiffAt
    ((domain_isOpen t r e).mem_nhds ((chart t r e).map_source hx))
  apply (hparam.comp x hfirst).congr_of_eventuallyEq
  filter_upwards [hc.eventually ((source_isOpen t r e).mem_nhds hx)] with y hy
  exact (param_coordinates t r e (g y) hy).symm

namespace BlowdownComplement

def baseAway (t : ℂ) : Set PlanePoint := {q | ∀ r, q ≠ centre r t}

def lift (t : ℂ) (q : PlanePoint) : Fiber t :=
  ⟨(q,fun r => chosenDirection q r t),fun r => chosenDirection_incidence q r t⟩

@[simp] theorem blowdown_lift (t : ℂ) (q : PlanePoint) : blowdown t (lift t q) = q := rfl

@[simp] theorem inclusion_lift (t : ℂ) (q : PlanePoint) :
    inclusion t (lift t q) = GlobalIncidence.BlowdownComplement.lift (q,t) := rfl

theorem lift_blowdown (t : ℂ) (p : Fiber t) (hp : p ∈ awayCentres t) :
    lift t (blowdown t p) = p := by
  apply inclusion_injective t
  exact GlobalIncidence.BlowdownComplement.lift_down (inclusion t p) hp

theorem blowdown_surjective (t : ℂ) : Function.Surjective (blowdown t) :=
  fun q => ⟨lift t q,rfl⟩

theorem baseAway_isOpen (t : ℂ) : IsOpen (baseAway t) := by
  rw [baseAway,setOf_forall]
  apply isOpen_iInter_of_finite
  intro r
  exact isOpen_ne_fun continuous_id continuous_const

theorem baseAway_dense (t : ℂ) : Dense (baseAway t) :=
  (blowdown_surjective t).denseRange.dense_of_mapsTo
    (blowdown_contMDiff t 0).continuous (awayCentres_dense t) (fun _ h => h)

theorem lift_contMDiffAt (t : ℂ) (n : WithTop ℕ∞) (q : PlanePoint)
    (hq : q ∈ baseAway t) :
    ContMDiffAt 𝓘(ℂ,ℂ × ℂ) 𝓘(ℂ,Coord) n (lift t) q := by
  apply contMDiffAt_of_total_inclusion t
  exact (GlobalIncidence.BlowdownComplement.lift_contMDiffAt n (q,t) hq).comp q
    (contMDiffAt_id.prodMk contMDiffAt_const)

def partialHomeomorph (t : ℂ) : PartialHomeomorph (Fiber t) PlanePoint where
  toFun := blowdown t
  invFun := lift t
  source := awayCentres t
  target := baseAway t
  map_source' _ h := h
  map_target' _ h := h
  left_inv' := lift_blowdown t
  right_inv' q _ := blowdown_lift t q
  open_source := awayCentres_isOpen t
  open_target := baseAway_isOpen t
  continuousOn_toFun := (blowdown_contMDiff t 0).continuous.continuousOn
  continuousOn_invFun := fun q hq => (lift_contMDiffAt t 0 q hq).continuousAt.continuousWithinAt

def homeomorph (t : ℂ) : awayCentres t ≃ₜ baseAway t :=
  (partialHomeomorph t).toHomeomorphSourceTarget

/-- A self-contained analytic modification certificate for each actual fibre. -/
theorem actual_fiber_proper_dense_open_biholomorphism (t : ℂ) :
    IsProperMap (blowdown t) ∧ Function.Surjective (blowdown t) ∧
      Dense (partialHomeomorph t).source ∧ Dense (partialHomeomorph t).target ∧
      ContMDiffOn 𝓘(ℂ,Coord) 𝓘(ℂ,ℂ × ℂ) ω
        (partialHomeomorph t) (partialHomeomorph t).source ∧
      ContMDiffOn 𝓘(ℂ,ℂ × ℂ) 𝓘(ℂ,Coord) ω
        (partialHomeomorph t).symm (partialHomeomorph t).target :=
  ⟨blowdown_isProperMap t,blowdown_surjective t,awayCentres_dense t,baseAway_dense t,
    (blowdown_contMDiff t ω).contMDiffOn,
    fun q hq => (lift_contMDiffAt t ω q hq).contMDiffWithinAt⟩
end BlowdownComplement
end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiber
