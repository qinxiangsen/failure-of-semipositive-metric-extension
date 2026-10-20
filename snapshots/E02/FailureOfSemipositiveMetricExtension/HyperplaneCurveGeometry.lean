import FailureOfSemipositiveMetricExtension.GenericConicAnalytic
import FailureOfSemipositiveMetricExtension.GlobalBlowdownComplement
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! The genuine hyperplane x+y+z=0, disjoint from all four centres for t ≠ -2.
Its lift is an actual closed holomorphic embedding in the given incidence fibre.
No numerical intersection-theory identification is asserted here. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.HyperplaneCurve
noncomputable section
open Set Topology IsManifold
open scoped Manifold ContDiff

structure Data where
  t : ℂ
  valid : t ≠ -2

def central : Data := ⟨0,by norm_num⟩

def embedding : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun v := ![v 0,v 1,-v 0-v 1]
  map_add' v w := by ext j; fin_cases j <;> simp <;> ring
  map_smul' a v := by ext j; fin_cases j <;> simp <;> ring

theorem embedding_injective : Function.Injective embedding := by
  intro v w h
  ext j
  fin_cases j
  · exact congrFun h 0
  · exact congrFun h 1

def base : Direction → PlanePoint := Projectivization.map embedding embedding_injective

theorem base_injective : Function.Injective base :=
  Projectivization.map_injective embedding embedding_injective

@[simp] theorem base_param (i : Fin 2) (s : ℂ) :
    base (ProjectiveLine.param i s) = ProjectivePlane.param i.castSucc (s,-1-s) := by
  fin_cases i
  · rfl
  · change Projectivization.mk ℂ ![s,1,-s-1] _ = Projectivization.mk ℂ ![s,1,-1-s] _
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    refine ⟨1,?_⟩
    ext j
    fin_cases j <;> simp <;> ring

def directionMap (c : Data) (r : Fin 4) : Blowup.Plane →ₗ[ℂ] Blowup.Plane :=
  (pairMap r c.t).comp embedding

theorem directionMap_eq_zero (c : Data) (r : Fin 4) (v : Blowup.Plane)
    (h : directionMap c r v = 0) : v = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  change pair r c.t (embedding v) 0 = 0 at h0
  change pair r c.t (embedding v) 1 = 0 at h1
  fin_cases r <;> simp [pair,embedding] at h0 h1
  · ext j; fin_cases j
    · change v 0 = 0
      linear_combination -h1-h0
    · exact h0
  · ext j; fin_cases j
    · exact h0
    · change v 1 = 0
      linear_combination -h1-h0
  · have hmul : (c.t+2)*v 0 = 0 := by linear_combination -h1-h0
    have ht : c.t+2 ≠ 0 := by intro hh; apply c.valid; linear_combination hh
    have hx := (mul_eq_zero.mp hmul).resolve_left ht
    ext j; fin_cases j
    · exact hx
    · change v 1 = 0
      linear_combination h0+hx
  · ext j; fin_cases j <;> assumption

theorem directionMap_injective (c : Data) (r : Fin 4) : Function.Injective (directionMap c r) := by
  intro v w h
  apply sub_eq_zero.mp
  apply directionMap_eq_zero c r
  rw [map_sub,h,sub_self]

theorem directionMap_nonzero (c : Data) (r : Fin 4) (v : Blowup.Plane) (hv : v ≠ 0) :
    directionMap c r v ≠ 0 := fun h => hv (directionMap_eq_zero c r v h)

def direction (c : Data) (r : Fin 4) : Direction → Direction :=
  Projectivization.map (directionMap c r) (directionMap_injective c r)

@[simp] theorem direction_three (c : Data) (d : Direction) : direction c 3 d = d := by
  induction d using Projectivization.ind with
  | h v hv =>
    change Projectivization.mk ℂ (directionMap c 3 v) _ = Projectivization.mk ℂ v hv
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    refine ⟨1,?_⟩
    ext j
    fin_cases j <;> simp [directionMap,embedding,pairMap,pair]

theorem incidence (c : Data) (d : Direction) (r : Fin 4) :
    Incidence (base d) (direction c r d) r c.t := by
  induction d using Projectivization.ind with
  | h v hv =>
    change Incidence (Projectivization.mk ℂ (embedding v) _) (Projectivization.mk ℂ (directionMap c r v) _) r c.t
    rw [incidence_mk_iff,Projectivization.submodule_mk]
    exact Submodule.mem_span_singleton_self _

/-- This is the genuine H lift, not a line through any blow-up centre. -/
def param (c : Data) (d : Direction) : Fiber c.t := ⟨(base d,fun r => direction c r d),incidence c d⟩

@[simp] theorem param_blowdown (c : Data) (d : Direction) : FixedFiber.blowdown c.t (param c d) = base d := rfl
@[simp] theorem param_direction (c : Data) (r : Fin 4) (d : Direction) :
    FixedFiber.direction c.t r (param c d) = direction c r d := rfl
@[simp] theorem param_direction_three (c : Data) (d : Direction) :
    FixedFiber.direction c.t 3 (param c d) = d := direction_three c d

theorem param_injective (c : Data) : Function.Injective (param c) := by
  intro d e h
  simpa using congrArg (FixedFiber.direction c.t 3) h

/-- Every point of the hyperplane avoids every centre. -/
theorem base_ne_centre (c : Data) (d : Direction) (r : Fin 4) : base d ≠ centre r c.t := by
  induction d using Projectivization.ind with
  | h v hv =>
    intro h
    apply directionMap_nonzero c r v hv
    change pairMap r c.t (embedding v) = 0
    apply (pairMap_zero_iff_mem_centre r c.t _).mpr
    exact (projective_eq_iff_mem _ _ _).mp h

theorem base_contMDiff (n : WithTop ℕ∞) : ContMDiff 𝓘(ℂ) 𝓘(ℂ,ℂ × ℂ) n base := by
  apply ProjectiveLine.contMDiff_of_param
  intro i
  simp only [base_param]
  exact (ProjectivePlane.param_contMDiff i.castSucc n).comp
    ((contDiff_id.prodMk (contDiff_const.sub contDiff_id)).contMDiff)

theorem directionMap_contDiff (c : Data) (r : Fin 4) (n : WithTop ℕ∞) :
    ContDiff ℂ n (directionMap c r) := (directionMap c r).toContinuousLinearMap.contDiff

theorem direction_contMDiff (c : Data) (r : Fin 4) (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) n (direction c r) := by
  apply ProjectiveLine.contMDiff_of_param
  intro i s
  have heq : (fun z => direction c r (ProjectiveLine.param i z)) =
      fun z => ProjectiveLine.vectorPoint (directionMap c r (ProjectiveLine.sourceVector i z)) := by
    funext z
    rw [ProjectiveLine.param_eq_mk_sourceVector,ProjectiveLine.vectorPoint_eq_mk _
      (directionMap_nonzero c r _ (ProjectiveLine.sourceVector_ne_zero i z))]
    rfl
  rw [heq]
  exact (ProjectiveLine.vectorPoint_contMDiffAt n _
    (directionMap_nonzero c r _ (ProjectiveLine.sourceVector_ne_zero i s))).comp s
    (((directionMap_contDiff c r n).comp (ProjectiveLine.sourceVector_contDiff i n)).contMDiff.contMDiffAt)

theorem param_contMDiff (c : Data) (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) n (param c) :=
  FixedFiber.contMDiff_of_structural_maps c.t 𝓘(ℂ) n (base_contMDiff n) (fun r => direction_contMDiff c r n)

theorem param_isClosedEmbedding (c : Data) : IsClosedEmbedding (param c) :=
  (param_contMDiff c 0).continuous.isClosedEmbedding (param_injective c)

theorem param_mfderiv_leftInverse (c : Data) (d : Direction) :
    (mfderiv 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) (FixedFiber.direction c.t 3) (param c d)).comp
      (mfderiv 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) (param c) d) =
        ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ) d) := by
  have hid : FixedFiber.direction c.t 3 ∘ param c = id := funext (param_direction_three c)
  apply ContinuousLinearMap.ext
  intro v
  have hc := mfderiv_comp_apply d
    (((FixedFiber.direction_contMDiff c.t 3 1) (param c d)).mdifferentiableAt le_rfl)
    (((param_contMDiff c 1) d).mdifferentiableAt le_rfl) v
  rw [hid,mfderiv_id] at hc
  exact hc.symm

theorem param_mfderiv_injective (c : Data) (d : Direction) :
    Function.Injective (mfderiv 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) (param c) d) :=
  (show Function.LeftInverse
    (mfderiv 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) (FixedFiber.direction c.t 3) (param c d))
    (mfderiv 𝓘(ℂ) 𝓘(ℂ,FixedFiber.Coord) (param c) d) from
      fun v => congrArg (fun T => T v) (param_mfderiv_leftInverse c d)).injective

/-- The entire inverse image of this hyperplane is its genuine strict transform. -/
theorem param_range (c : Data) : range (param c) = (FixedFiber.blowdown c.t) ⁻¹' range base := by
  ext p
  constructor
  · rintro ⟨d,rfl⟩; exact ⟨d,rfl⟩
  · rintro ⟨d,hd⟩
    refine ⟨d,?_⟩
    apply FixedFiber.inclusion_injective c.t
    apply total_ext
    · exact hd
    · funext r
      exact directions_eq_away _ _ r hd rfl (base_ne_centre c d r)
    · rfl

/-- Closure-of-away-points definition, using the original blowdown and centres. -/
def strictTransform (c : Data) : Set (Fiber c.t) :=
  closure {p | FixedFiber.blowdown c.t p ∈ range base ∧ ∀ r, FixedFiber.blowdown c.t p ≠ centre r c.t}

theorem param_range_strictTransform (c : Data) : range (param c) = strictTransform c := by
  have hs : {p : Fiber c.t | FixedFiber.blowdown c.t p ∈ range base ∧
      ∀ r, FixedFiber.blowdown c.t p ≠ centre r c.t} = range (param c) := by
    rw [param_range]
    ext p
    constructor
    · exact And.left
    · rintro ⟨d,hd⟩
      exact ⟨⟨d,hd⟩,fun r => hd ▸ base_ne_centre c d r⟩
  rw [strictTransform,hs,(param_isClosedEmbedding c).isClosed_range.closure_eq]

/-- In particular, all four actual exceptional fibres are disjoint from H. -/
theorem disjoint_exceptional (c : Data) (r : Fin 4) :
    Disjoint (range (param c)) {p : Fiber c.t | FixedFiber.blowdown c.t p = centre r c.t} := by
  rw [Set.disjoint_left]
  rintro _ ⟨d,rfl⟩ hp
  exact base_ne_centre c d r hp

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.HyperplaneCurve
