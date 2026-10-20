import FailureOfSemipositiveMetricExtension.HisamotoBlowupComparison

/-! Off the centre the one-point projective incidence blowdown is a genuine
analytic isomorphism. Together with the actual affine blowup comparison this
certifies the entire analytic blowup by its standard open cover. -/
namespace FailureOfSemipositiveMetricExtension.Hisamoto
noncomputable section
open Set Topology
open scoped Manifold ContDiff

/-- The rational direction `[y:z]`, with an arbitrary value only at the centre. -/
def planeDirection (p : PlanePoint) : Direction := ProjectiveLine.vectorPoint (centrePair p.rep)

theorem planeDirection_mk (v : Fin 3 → ℂ) (hv : v ≠ 0) :
    planeDirection (Projectivization.mk ℂ v hv) = ProjectiveLine.vectorPoint (centrePair v) := by
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  unfold planeDirection
  rw [← ha]
  change ProjectiveLine.vectorPoint (centrePair ((a : ℂ) • v)) = _
  rw [map_smul]
  exact vectorPoint_smul a _

theorem planeDirection_incidence (p : PlanePoint) : Incidence p (planeDirection p) := by
  rw [← Projectivization.mk_rep p,incidence_mk_iff,Projectivization.mk_rep]
  change centrePair p.rep ∈ (ProjectiveLine.vectorPoint (centrePair p.rep)).submodule
  by_cases hz : centrePair p.rep = 0
  · rw [hz]; exact Submodule.zero_mem _
  · rw [ProjectiveLine.vectorPoint_eq_mk _ hz,Projectivization.submodule_mk]
    exact Submodule.mem_span_singleton_self _

theorem centrePair_rep_nonzero (p : PlanePoint) (hp : p ≠ centre) : centrePair p.rep ≠ 0 := by
  intro h
  apply hp
  simpa only [Projectivization.mk_rep] using (centrePair_zero_iff p.rep p.rep_nonzero).mp h

theorem incidence_unique_away (p : PlanePoint) (hp : p ≠ centre) (d : Direction) (hd : Incidence p d) :
    d = planeDirection p := by
  rw [← Projectivization.mk_rep p,incidence_mk_iff] at hd
  unfold planeDirection
  rw [ProjectiveLine.vectorPoint_eq_mk _ (centrePair_rep_nonzero p hp)]
  rw [← Projectivization.mk_rep d,Projectivization.submodule_mk,Submodule.mem_span_singleton] at hd
  symm
  rw [← Projectivization.mk_rep d]
  exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr hd

theorem centrePair_contDiff (n : WithTop ℕ∞) : ContDiff ℂ n centrePair := by
  apply contDiff_pi.mpr
  intro j
  fin_cases j <;> dsimp [centrePair] <;> fun_prop

theorem planeDirection_contMDiffAt (n : WithTop ℕ∞) (p : PlanePoint) (hp : p ≠ centre) :
    ContMDiffAt 𝓘(ℂ,Coord) 𝓘(ℂ) n planeDirection p := by
  obtain ⟨a,v,hv⟩ := ProjectivePlane.charts_cover p
  have ha : p ∈ ProjectivePlane.chartSet a := ⟨v,hv.symm⟩
  have hn : centrePair (ProjectivePlane.vector a (ProjectivePlane.coordinates a p)) ≠ 0 := by
    intro hz
    apply hp
    have h := (centrePair_zero_iff _ (ProjectivePlane.vector_nonzero a _)).mp hz
    change ProjectivePlane.param a (ProjectivePlane.coordinates a p) = centre at h
    rwa [ProjectivePlane.param_coordinates a p ha] at h
  have hc := (ProjectivePlaneBundle.coordinates_contMDiffOn a n).contMDiffAt
    ((ProjectivePlane.chartSet_isOpen a).mem_nhds ha)
  have hm := ((centrePair_contDiff n).comp (planeVector_contDiff a n)).contMDiff.contMDiffAt.comp p hc
  apply ((ProjectiveLine.vectorPoint_contMDiffAt n _ hn).comp p hm).congr_of_eventuallyEq
  filter_upwards [(ProjectivePlane.chartSet_isOpen a).mem_nhds ha] with p' hp'
  have he := planeDirection_mk (ProjectivePlane.vector a (ProjectivePlane.coordinates a p'))
    (ProjectivePlane.vector_nonzero a _)
  change planeDirection (ProjectivePlane.param a (ProjectivePlane.coordinates a p')) = _ at he
  rwa [ProjectivePlane.param_coordinates a p' hp'] at he

def liftPlane (p : PlanePoint) : Point := ⟨(p,planeDirection p),planeDirection_incidence p⟩
@[simp] theorem blowdown_liftPlane (p : PlanePoint) : blowdown (liftPlane p) = p := rfl

theorem liftPlane_blowdown (q : Point) (hq : blowdown q ≠ centre) : liftPlane (blowdown q) = q := by
  apply point_ext
  · rfl
  · exact (incidence_unique_away (blowdown q) hq (ruling q) q.property).symm

/-- Analyticity into the actual incidence manifold follows from its verified
analytic projective components and local inverse coordinate maps. -/
theorem contMDiffAt_of_components {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℂ E H) (n : WithTop ℕ∞) {f : M → Point} {x : M}
    (hp : ContMDiffAt I 𝓘(ℂ,Coord) n (fun y => blowdown (f y)) x)
    (hd : ContMDiffAt I 𝓘(ℂ) n (fun y => ruling (f y)) x) :
    ContMDiffAt I 𝓘(ℂ,Coord) n f x := by
  obtain ⟨⟨i,j⟩,hx⟩ := affineCharts_cover (f x)
  have hm := (mem_affineChart_source i j (f x)).mp hx
  have hf := (fiberDirection_contMDiffAt i n (blowdown (f x))
    (fiberProjection_rep_nonzero i (f x) hm.1)).comp x hp
  have hc := ((ProjectiveLineBundle.coordinates_contMDiffOn j n).contMDiffAt
    ((ProjectiveLine.chartSet_isOpen j).mem_nhds hm.2)).comp x hf
  have ht := ((ProjectiveLineBundle.coordinates_contMDiffOn i n).contMDiffAt
    ((ProjectiveLine.chartSet_isOpen i).mem_nhds hm.1)).comp x hd
  have hh := (affineParam_contMDiff i j n).contMDiffAt.comp x (hc.prodMk_space ht)
  have hcont : ContinuousAt f x := (hp.continuousAt.prodMk hd.continuousAt).codRestrict _
  apply hh.congr_of_eventuallyEq
  filter_upwards [hcont.eventually ((affineChart i j).open_source.mem_nhds hx)] with y hy
  exact ((affineChart i j).left_inv hy).symm

theorem liftPlane_contMDiffAt (n : WithTop ℕ∞) (p : PlanePoint) (hp : p ≠ centre) :
    ContMDiffAt 𝓘(ℂ,Coord) 𝓘(ℂ,Coord) n liftPlane p :=
  contMDiffAt_of_components _ n contMDiffAt_id (planeDirection_contMDiffAt n p hp)

def awayCentre : Set Point := {q | blowdown q ≠ centre}
def puncturedPlane : Set PlanePoint := {p | p ≠ centre}

theorem awayCentre_isOpen : IsOpen awayCentre := isOpen_ne_fun blowdown_continuous continuous_const
theorem puncturedPlane_isOpen : IsOpen puncturedPlane := isOpen_ne

/-- The blowdown is an actual two-sided analytic isomorphism outside E. -/
def blowdownComplementChart : PartialHomeomorph Point PlanePoint where
  toFun := blowdown
  invFun := liftPlane
  source := awayCentre
  target := puncturedPlane
  map_source' _ h := h
  map_target' _ h := h
  left_inv' := liftPlane_blowdown
  right_inv' := fun p _ => blowdown_liftPlane p
  open_source := awayCentre_isOpen
  open_target := puncturedPlane_isOpen
  continuousOn_toFun := blowdown_continuous.continuousOn
  continuousOn_invFun := fun p hp => (liftPlane_contMDiffAt 0 p hp).continuousAt.continuousWithinAt

theorem blowdownComplement_analytic :
    ContMDiffOn 𝓘(ℂ,Coord) 𝓘(ℂ,Coord) ω blowdown awayCentre ∧
      ContMDiffOn 𝓘(ℂ,Coord) 𝓘(ℂ,Coord) ω liftPlane puncturedPlane :=
  ⟨(blowdown_contMDiff ω).contMDiffOn,fun p hp => (liftPlane_contMDiffAt ω p hp).contMDiffWithinAt⟩

/-- The standard affine blowup and the unmodified complement cover the whole
actual projective incidence surface. -/
theorem standard_blowup_open_cover : centreAffine ∪ awayCentre = univ := by
  ext q
  simp only [mem_union,mem_univ,iff_true]
  by_cases h : blowdown q = centre
  · left
    change blowdown q ∈ ProjectivePlane.chartSet 0
    rw [h]
    exact ⟨(0,0),rfl⟩
  · exact Or.inr h

end
end FailureOfSemipositiveMetricExtension.Hisamoto
