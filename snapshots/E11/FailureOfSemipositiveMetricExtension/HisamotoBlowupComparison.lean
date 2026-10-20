import FailureOfSemipositiveMetricExtension.HisamotoExceptionalDivisor
import FailureOfSemipositiveMetricExtension.BlowupManifold

/-! The one-point projective incidence surface restricts over the affine plane
containing the centre to the already constructed actual affine blowup. This
comparison respects blowdown, exceptional fibres, topology, and analytic charts. -/
namespace FailureOfSemipositiveMetricExtension.Hisamoto
noncomputable section
open Set Topology IsManifold
open scoped Manifold ContDiff
attribute [local instance] Classical.propDecidable

/-- The preimage of the centre's standard affine neighbourhood. -/
def centreAffine : Set Point := blowdown ⁻¹' ProjectivePlane.chartSet 0

def fromAffineBlowup (u : Blowup.Point) : Point :=
  ⟨(ProjectivePlane.param 0 (Blowup.projection u 0,Blowup.projection u 1),Blowup.direction u),by
    rw [ProjectivePlane.param,incidence_mk_iff]
    convert u.property using 1
    ext j
    fin_cases j <;> rfl⟩

@[simp] theorem fromAffineBlowup_blowdown (u : Blowup.Point) :
    blowdown (fromAffineBlowup u) = ProjectivePlane.param 0 (Blowup.projection u 0,Blowup.projection u 1) := rfl
@[simp] theorem fromAffineBlowup_ruling (u : Blowup.Point) :
    ruling (fromAffineBlowup u) = Blowup.direction u := rfl

theorem fromAffineBlowup_mem (u : Blowup.Point) : fromAffineBlowup u ∈ centreAffine :=
  ⟨_,rfl⟩

theorem fromAffineBlowup_injective : Function.Injective fromAffineBlowup := by
  intro u v h
  have hp := ProjectivePlane.param_injective 0 (congrArg blowdown h)
  apply Blowup.point_ext
  · ext j
    fin_cases j
    · exact congrArg Prod.fst hp
    · exact congrArg Prod.snd hp
  · exact congrArg ruling h

def toAffineBlowup (q : centreAffine) : Blowup.Point :=
  ⟨(![(ProjectivePlane.coordinates 0 (blowdown q.val)).1,
    (ProjectivePlane.coordinates 0 (blowdown q.val)).2],ruling q.val),by
      have hi : Incidence (ProjectivePlane.param 0 (ProjectivePlane.coordinates 0 (blowdown q.val)))
          (ruling q.val) := by rw [ProjectivePlane.param_coordinates 0 _ q.property]; exact q.val.property
      exact (incidence_mk_iff _ _ _).mp hi⟩

theorem fromAffineBlowup_toAffine (q : centreAffine) : fromAffineBlowup (toAffineBlowup q) = q.val := by
  apply point_ext
  · exact ProjectivePlane.param_coordinates 0 _ q.property
  · rfl

def affineBlowupEquiv : Blowup.Point ≃ centreAffine where
  toFun u := ⟨fromAffineBlowup u,fromAffineBlowup_mem u⟩
  invFun := toAffineBlowup
  left_inv u := fromAffineBlowup_injective (fromAffineBlowup_toAffine _)
  right_inv q := Subtype.ext (fromAffineBlowup_toAffine q)

@[simp] theorem fromAffineBlowup_X (q : Coord) :
    fromAffineBlowup (Blowup.X q.1 q.2) = affineParam 0 0 q := by
  apply point_ext
  · change ProjectivePlane.param 0 (q.1,q.1*q.2) = fiberPlane 0 q.2 (ProjectiveLine.param 0 q.1)
    exact (fiberPlane_param_planeParam 0 0 q).symm
  · rfl
@[simp] theorem fromAffineBlowup_Y (q : Coord) :
    fromAffineBlowup (Blowup.Y q.1 q.2) = affineParam 1 0 q := by
  apply point_ext
  · change ProjectivePlane.param 0 (q.1*q.2,q.1) = fiberPlane 1 q.2 (ProjectiveLine.param 0 q.1)
    exact (fiberPlane_param_planeParam 1 0 q).symm
  · rfl

theorem fromAffineBlowup_contMDiff (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ,Coord) 𝓘(ℂ,Coord) n fromAffineBlowup := by
  intro u
  rcases Blowup.charts_cover u with ⟨r,s,rfl⟩ | ⟨r,s,rfl⟩
  · have hu : Blowup.X r s ∈ Blowup.homeomorphChartX.source := ⟨s,rfl⟩
    have hc := (contMDiffOn_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ,Coord)) (n := n)
        ((Blowup.mem_atlas_iff _).mpr (Or.inl rfl)))).contMDiffAt
          (Blowup.homeomorphChartX.open_source.mem_nhds hu)
    apply ((affineParam_contMDiff 0 0 n).contMDiffAt.comp _ hc).congr_of_eventuallyEq
    filter_upwards [Blowup.homeomorphChartX.open_source.mem_nhds hu] with v hv
    change fromAffineBlowup v = affineParam 0 0 (Blowup.homeomorphChartX v)
    rw [← fromAffineBlowup_X]
    exact congrArg fromAffineBlowup (Blowup.homeomorphChartX.left_inv hv).symm
  · have hu : Blowup.Y r s ∈ Blowup.homeomorphChartY.source := ⟨s,rfl⟩
    have hc := (contMDiffOn_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ,Coord)) (n := n)
        ((Blowup.mem_atlas_iff _).mpr (Or.inr rfl)))).contMDiffAt
          (Blowup.homeomorphChartY.open_source.mem_nhds hu)
    apply ((affineParam_contMDiff 1 0 n).contMDiffAt.comp _ hc).congr_of_eventuallyEq
    filter_upwards [Blowup.homeomorphChartY.open_source.mem_nhds hu] with v hv
    change fromAffineBlowup v = affineParam 1 0 (Blowup.homeomorphChartY v)
    rw [← fromAffineBlowup_Y]
    exact congrArg fromAffineBlowup (Blowup.homeomorphChartY.left_inv hv).symm

theorem affineChart_source_iff_plane (i j : Fin 2) (q : Point) :
    q ∈ (affineChart i j).source ↔ q ∈ rulingChart i ∧
      blowdown q ∈ ProjectivePlane.chartSet (planeIndex i j) := by
  constructor
  · intro h
    exact ⟨((mem_affineChart_source i j q).mp h).1,planeChart_of_affineChart i j q h⟩
  · rintro ⟨hi,hp⟩
    apply (mem_affineChart_source i j q).mpr
    refine ⟨hi,?_⟩
    have he := localParam_localCoordinates i q hi
    have hb := congrArg blowdown he
    rw [← hb,blowdown_localParam,fiberPlane_mem_planeChart_iff] at hp
    exact hp

/-- Extended arbitrarily outside the open set, as usual for partial analytic maps. -/
def inverseAffineBlowup (q : Point) : Blowup.Point :=
  if h : q ∈ centreAffine then toAffineBlowup ⟨q,h⟩ else Blowup.X 0 0

theorem inverseAffineBlowup_fromAffine (u : Blowup.Point) :
    inverseAffineBlowup (fromAffineBlowup u) = u := by
  simp only [inverseAffineBlowup,dif_pos (fromAffineBlowup_mem u)]
  exact affineBlowupEquiv.left_inv u

theorem fromAffineBlowup_inverse (q : Point) (hq : q ∈ centreAffine) :
    fromAffineBlowup (inverseAffineBlowup q) = q := by
  simp only [inverseAffineBlowup,dif_pos hq]
  exact fromAffineBlowup_toAffine ⟨q,hq⟩

theorem centreAffine_isOpen : IsOpen centreAffine :=
  (ProjectivePlane.chartSet_isOpen 0).preimage blowdown_continuous

theorem inverseAffineBlowup_contMDiffOn (n : WithTop ℕ∞) :
    ContMDiffOn 𝓘(ℂ,Coord) 𝓘(ℂ,Coord) n inverseAffineBlowup centreAffine := by
  intro q hq
  obtain ⟨i,hi⟩ := ruling_charts_cover q
  have ha : q ∈ (affineChart i 0).source :=
    (affineChart_source_iff_plane i 0 q).mpr ⟨hi,hq⟩
  have hc := (affineCoordinates_contMDiffOn i 0 n).contMDiffAt ((affineChart i 0).open_source.mem_nhds ha)
  fin_cases i
  · have hx := contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ,Coord)) (n := n)
        ((Blowup.mem_atlas_iff _).mpr (Or.inl rfl)))
    rw [Blowup.homeomorphChartX_target] at hx
    have hh := (contMDiffOn_univ.mp hx).contMDiffAt.comp q hc
    apply (hh.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [(affineChart 0 0).open_source.mem_nhds ha,centreAffine_isOpen.mem_nhds hq] with p hp hp'
    apply fromAffineBlowup_injective
    rw [fromAffineBlowup_inverse p hp']
    change p = fromAffineBlowup (Blowup.X _ _)
    rw [fromAffineBlowup_X]
    exact ((affineChart 0 0).left_inv hp).symm
  · have hx := contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ,Coord)) (n := n)
        ((Blowup.mem_atlas_iff _).mpr (Or.inr rfl)))
    rw [Blowup.homeomorphChartY_target] at hx
    have hh := (contMDiffOn_univ.mp hx).contMDiffAt.comp q hc
    apply (hh.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [(affineChart 1 0).open_source.mem_nhds ha,centreAffine_isOpen.mem_nhds hq] with p hp hp'
    apply fromAffineBlowup_injective
    rw [fromAffineBlowup_inverse p hp']
    change p = fromAffineBlowup (Blowup.Y _ _)
    rw [fromAffineBlowup_Y]
    exact ((affineChart 1 0).left_inv hp).symm

/-- A concrete biholomorphic comparison with the actual affine-origin blowup. -/
def affineBlowupChart : PartialHomeomorph Point Blowup.Point where
  toFun := inverseAffineBlowup
  invFun := fromAffineBlowup
  source := centreAffine
  target := univ
  map_source' _ _ := mem_univ _
  map_target' u _ := fromAffineBlowup_mem u
  left_inv' := fromAffineBlowup_inverse
  right_inv' u _ := inverseAffineBlowup_fromAffine u
  open_source := centreAffine_isOpen
  open_target := isOpen_univ
  continuousOn_toFun := (inverseAffineBlowup_contMDiffOn 0).continuousOn
  continuousOn_invFun := (fromAffineBlowup_contMDiff 0).continuous.continuousOn

/-- The centre fibre agrees literally with the usual affine exceptional fibre. -/
theorem fromAffineBlowup_exceptional_iff (u : Blowup.Point) :
    fromAffineBlowup u ∈ exceptionalSet ↔ Blowup.projection u = 0 := by
  change ProjectivePlane.param 0 _ = ProjectivePlane.param 0 (0,0) ↔ _
  rw [(ProjectivePlane.param_injective 0).eq_iff]
  constructor
  · intro h
    ext j
    fin_cases j
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  · intro h
    simp [h]

end
end FailureOfSemipositiveMetricExtension.Hisamoto
