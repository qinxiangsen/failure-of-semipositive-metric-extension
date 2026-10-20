import FailureOfSemipositiveMetricExtension.GlobalAffineCentres
import FailureOfSemipositiveMetricExtension.ProjectiveLine

/-!
Eight genuine set charts for the global four-centre incidence total space.
Each centre is normalized in a projective affine block, then its actual affine
blow-up is parametrized in either standard chart. The other three centres are
removed from that chart domain. Coverage, injectivity, and both inverse laws
are proved; this file alone does not install a global topology or analytic atlas.
-/

namespace FailureOfSemipositiveMetricExtension.GlobalIncidence
noncomputable section

open Set

/-- The two actual affine blow-up parametrizations, uniformly indexed. -/
def localParam (e : Fin 2) (q : ℂ × ℂ) : Blowup.Point :=
  if e = 0 then Blowup.X q.1 q.2 else Blowup.Y q.1 q.2

theorem localParam_injective (e : Fin 2) : Function.Injective (localParam e) := by
  fin_cases e
  · exact Blowup.X_injective
  · exact Blowup.Y_injective

theorem localParams_cover (b : Blowup.Point) : ∃ e q, b = localParam e q := by
  rcases Blowup.charts_cover b with ⟨r,s,h⟩ | ⟨r,s,h⟩
  · exact ⟨0,(r,s),h⟩
  · exact ⟨1,(r,s),h⟩

/-- Lift a point of the actual affine blow-up to the corresponding global incidence model.
Other directions use the canonical incidence direction; chart domains below exclude their centres. -/
def localLift (i : Fin 4) (b : Blowup.Point) (t : ℂ) : Total :=
  ⟨(affineBase i t (Blowup.projection b),
    (fun j => if j = i then Blowup.direction b
      else chosenDirection (affineBase i t (Blowup.projection b)) j t),t),by
    intro j
    dsimp only
    split_ifs with hj
    · subst j
      exact (incidence_affineBase_iff i t (Blowup.projection b) (Blowup.direction b)).mpr b.property
    · exact chosenDirection_incidence _ j t⟩

@[simp] theorem localLift_blowdown (i : Fin 4) (b : Blowup.Point) (t : ℂ) :
    blowdown (localLift i b t) = affineBase i t (Blowup.projection b) := rfl
@[simp] theorem localLift_projection (i : Fin 4) (b : Blowup.Point) (t : ℂ) :
    projection (localLift i b t) = t := rfl
@[simp] theorem localLift_direction (i : Fin 4) (b : Blowup.Point) (t : ℂ) :
    directions (localLift i b t) i = Blowup.direction b := by
  simp [directions,localLift]

theorem localLift_injective (i : Fin 4) :
    Function.Injective (fun q : Blowup.Point × ℂ => localLift i q.1 q.2) := by
  intro q q' h
  have ht : q.2 = q'.2 := congrArg projection h
  apply Prod.ext
  · apply Blowup.point_ext
    · have hb := congrArg blowdown h
      simp only [localLift_blowdown,ht] at hb
      exact affineBase_injective i q'.2 hb
    · simpa only [localLift_direction] using congrArg (fun p => directions p i) h
  · exact ht

/-- Away from the other centres, local incidence data recover the original global point. -/
theorem localLift_eq_of_data (i : Fin 4) (b : Blowup.Point) (t : ℂ) (p : Total)
    (hb : affineBase i t (Blowup.projection b) = blowdown p)
    (hd : Blowup.direction b = directions p i) (ht : t = projection p)
    (haway : ∀ j, j ≠ i → blowdown p ≠ centre j (projection p)) :
    localLift i b t = p := by
  apply total_ext (p := localLift i b t) (q := p) hb _ ht
  funext j
  by_cases hj : j = i
  · subst j
    simpa only [localLift_direction] using hd
  · apply directions_eq_away (localLift i b t) p j hb ht
    change affineBase i t (Blowup.projection b) ≠ centre j t
    rw [hb,ht]
    exact haway j hj

/-- Affine three-space coordinates: two blow-up coordinates and the family parameter. -/
abbrev ChartCoord := (ℂ × ℂ) × ℂ

/-- Eight explicit parametrizations into the actual global total space. -/
def chartParam (i : Fin 4) (e : Fin 2) (q : ChartCoord) : Total :=
  localLift i (localParam e q.1) q.2

theorem chartParam_injective (i : Fin 4) (e : Fin 2) : Function.Injective (chartParam i e) := by
  intro q q' h
  have he := @localLift_injective i (localParam e q.1,q.2) (localParam e q'.1,q'.2) h
  apply Prod.ext
  · exact localParam_injective e (congrArg (fun x : Blowup.Point × ℂ => x.1) he)
  · exact congrArg (fun x : Blowup.Point × ℂ => x.2) he

/-- The chart omits the other three centres, whose exceptional directions require their own charts. -/
def chartDomain (i : Fin 4) (e : Fin 2) : Set ChartCoord :=
  {q | ∀ j, j ≠ i →
    affineBase i q.2 (Blowup.projection (localParam e q.1)) ≠ centre j q.2}

/-- The actual subset of the global incidence space parametrized by each chart domain. -/
def chartSource (i : Fin 4) (e : Fin 2) : Set Total := chartParam i e '' chartDomain i e

/-- Global extensions of inverse coordinates; only source-domain values are used. -/
def chartCoordinates (i : Fin 4) (e : Fin 2) : Total → ChartCoord :=
  Function.invFun (chartParam i e)

@[simp] theorem chartCoordinates_param (i : Fin 4) (e : Fin 2) (q : ChartCoord) :
    chartCoordinates i e (chartParam i e q) = q :=
  Function.leftInverse_invFun (chartParam_injective i e) q

theorem chartParam_coordinates (i : Fin 4) (e : Fin 2) (p : Total)
    (hp : p ∈ chartSource i e) : chartParam i e (chartCoordinates i e p) = p := by
  rcases hp with ⟨q,_,rfl⟩
  rw [chartCoordinates_param]

/-- A genuine partial equivalence, with both inverse laws proved on its specified sets. -/
def partialChart (i : Fin 4) (e : Fin 2) : PartialEquiv Total ChartCoord where
  toFun := chartCoordinates i e
  invFun := chartParam i e
  source := chartSource i e
  target := chartDomain i e
  map_source' p hp := by
    rcases hp with ⟨q,hq,rfl⟩
    simpa using hq
  map_target' q hq := ⟨q,hq,rfl⟩
  left_inv' := chartParam_coordinates i e
  right_inv' q _ := chartCoordinates_param i e q

@[simp] theorem partialChart_source (i : Fin 4) (e : Fin 2) :
    (partialChart i e).source = chartSource i e := rfl
@[simp] theorem partialChart_target (i : Fin 4) (e : Fin 2) :
    (partialChart i e).target = chartDomain i e := rfl
@[simp] theorem partialChart_symm_apply (i : Fin 4) (e : Fin 2) (q : ChartCoord) :
    (partialChart i e).symm q = chartParam i e q := rfl

/-- The eight coordinate domains genuinely cover every point of the global incidence space. -/
theorem global_charts_cover (p : Total) :
    ∃ i e q, q ∈ chartDomain i e ∧ p = chartParam i e q := by
  obtain ⟨i,w,hp,haway⟩ := affineBase_cover_avoiding (blowdown p) (projection p)
  have hm : w ∈ (directions p i).submodule := by
    apply (incidence_affineBase_iff i (projection p) w (directions p i)).mp
    rw [← hp]
    exact p.property i
  let b : Blowup.Point := ⟨(w,directions p i),hm⟩
  obtain ⟨e,q,hq⟩ := localParams_cover b
  have hlift : localLift i b (projection p) = p :=
    localLift_eq_of_data i b (projection p) p hp.symm rfl rfl haway
  refine ⟨i,e,(q,projection p),?_,?_⟩
  · intro j hj
    change affineBase i (projection p) (Blowup.projection (localParam e q)) ≠ _
    rw [← hq]
    change affineBase i (projection p) w ≠ _
    rw [← hp]
    exact haway j hj
  · change p = localLift i (localParam e q) (projection p)
    rw [← hq]
    exact hlift.symm

/-- The sources of the constructed partial equivalences cover the actual total space. -/
theorem iUnion_chartSource : (⋃ i, ⋃ e, chartSource i e) = univ := by
  apply Set.eq_univ_of_forall
  intro p
  obtain ⟨i,e,q,hq,hp⟩ := global_charts_cover p
  exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨e,q,hq,hp.symm⟩⟩

@[simp] theorem localParam_direction (e : Fin 2) (q : ℂ × ℂ) :
    Blowup.direction (localParam e q) = ProjectiveLine.param e q.2 := by
  fin_cases e <;> rfl

/-- Membership in either affine blow-up chart is exactly membership of its projective direction. -/
theorem localParam_range_iff (e : Fin 2) (b : Blowup.Point) :
    (∃ q, b = localParam e q) ↔ Blowup.direction b ∈ ProjectiveLine.chartSet e := by
  fin_cases e
  · change (∃ q : ℂ × ℂ, b = Blowup.X q.1 q.2) ↔
      ∃ s, Blowup.lineX s = Blowup.direction b
    constructor
    · rintro ⟨q,rfl⟩
      exact ⟨q.2,rfl⟩
    · rintro ⟨s,hs⟩
      exact ⟨(Blowup.projection b 0,s),Blowup.eq_X_of_direction b s hs.symm⟩
  · change (∃ q : ℂ × ℂ, b = Blowup.Y q.1 q.2) ↔
      ∃ s, Blowup.lineY s = Blowup.direction b
    constructor
    · rintro ⟨q,rfl⟩
      exact ⟨q.2,rfl⟩
    · rintro ⟨s,hs⟩
      exact ⟨(Blowup.projection b 1,s),Blowup.eq_Y_of_direction b s hs.symm⟩

/-- An intrinsic source description, involving only the base affine block, one direction
chart, and avoidance of the other three centre sections. -/
theorem mem_chartSource_iff (i : Fin 4) (e : Fin 2) (p : Total) :
    p ∈ chartSource i e ↔
      blowdown p ∈ ProjectivePlane.chartSet (baseChart i) ∧
      directions p i ∈ ProjectiveLine.chartSet e ∧
      ∀ j, j ≠ i → blowdown p ≠ centre j (projection p) := by
  constructor
  · rintro ⟨q,hq,rfl⟩
    refine ⟨affineBase_mem_chartSet i q.2 (Blowup.projection (localParam e q.1)),?_,hq⟩
    simp only [chartParam,localLift_direction,localParam_direction]
    exact ⟨q.1.2,rfl⟩
  · rintro ⟨hb,hd,haway⟩
    rw [← affineBase_range i (projection p)] at hb
    obtain ⟨w,hw⟩ := hb
    have hm : w ∈ (directions p i).submodule := by
      apply (incidence_affineBase_iff i (projection p) w (directions p i)).mp
      rw [hw]
      exact p.property i
    let b : Blowup.Point := ⟨(w,directions p i),hm⟩
    obtain ⟨q,hq⟩ := (localParam_range_iff e b).mpr hd
    have hlift : localLift i b (projection p) = p :=
      localLift_eq_of_data i b (projection p) p hw rfl rfl haway
    refine ⟨(q,projection p),?_,?_⟩
    · intro j hj
      change affineBase i (projection p) (Blowup.projection (localParam e q)) ≠ _
      rw [← hq]
      change affineBase i (projection p) w ≠ _
      rw [hw]
      exact haway j hj
    · change localLift i (localParam e q) (projection p) = p
      rw [← hq]
      exact hlift

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence
